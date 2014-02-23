/*******************************************************************\

Module: Job Status

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cstdlib>
#include <fstream>
#include <set>

// for strptime
#ifndef _XOPEN_SOURCE
#define _XOPEN_SOURCE
#endif

#include <time.h>
#include <dirent.h>
#include <unistd.h>

#include <util/xml.h>
#include <util/cout_message.h>
#include <util/suffix.h>

#include <xmllang/xml_parser.h>

#include "git_log.h"
#include "job_status.h"

/*******************************************************************\

Function: job_statust::set_hostname

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void job_statust::set_hostname()
{
  char s[1000];
  if(gethostname(s, 1000)==0)
  {
    hostname=std::string(s);
  }        
}

/*******************************************************************\

Function: job_statust::next_stage

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void job_statust::next_stage()
{
  assert(stage!=DONE);
  stage=(staget)((int)stage+1);
  status=stage==DONE?COMPLETED:WAITING;
}

/*******************************************************************\

Function: job_statust::read

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void job_statust::read()
{
  xmlt src;
  
  console_message_handlert message_handler;
      
  if(parse_xml("jobs/"+id+".status", message_handler, src))
  {
    // assume it's new
    clear();
    return;
  }

  if(src.name!="deltagit_jobstatus")
    throw std::string("unexpected XML for job status");

  const std::string stage_string=src.get_attribute("stage");
  
  if(stage_string=="init")
    stage=INIT;
  else if(stage_string=="check out")
    stage=CHECK_OUT;
  else if(stage_string=="build")
    stage=BUILD;
  else if(stage_string=="analyse")
    stage=ANALYSE;
  else if(stage_string=="done")
    stage=DONE;
  else
    throw std::string("unexpected stage");

  const std::string status_string=src.get_attribute("status");
  
  if(status_string=="waiting")
    status=WAITING;
  else if(status_string=="running")
    status=RUNNING;
  else if(status_string=="failure")
    status=FAILURE;
  else if(status_string=="completed")
    status=COMPLETED;
  else
    throw std::string("unexpected status");

  added=atol(src.get_attribute("added").c_str());
  deleted=atol(src.get_attribute("deleted").c_str());
  message=src.get_element("message");
  author=src.get_attribute("author");
  date=src.get_attribute("date");
  commit=src.get_attribute("commit");

  hostname=src.get_attribute("hostname");
}

/*******************************************************************\

Function: as_string

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string as_string(job_statust::staget stage)
{
  switch(stage)
  {
  case job_statust::INIT: return "init";
  case job_statust::CHECK_OUT: return "check out";
  case job_statust::BUILD: return "build";
  case job_statust::ANALYSE: return "analyse";
  case job_statust::DONE: return "done";
  default: return "";
  }
}

/*******************************************************************\

Function: as_string

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string as_string(job_statust::statust status)
{
  switch(status)
  {
  case job_statust::WAITING: return "waiting";
  case job_statust::RUNNING: return "running";
  case job_statust::FAILURE: return "failure";
  case job_statust::COMPLETED: return "completed";
  default: return "";
  }
}

/*******************************************************************\

Function: job_statust::write

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void job_statust::write()
{
  xmlt xml;
  xml.name="deltagit_jobstatus";

  xml.set_attribute("id", id);
  xml.set_attribute("status", as_string(status));
  xml.set_attribute("stage", as_string(stage));
  xml.set_attribute("commit", commit);
  xml.set_attribute("added", added);
  xml.set_attribute("deleted", deleted);
  xml.set_attribute("author", author);
  xml.set_attribute("date", date);
  xml.set_attribute("hostname", hostname);
  xml.new_element("message").data=message;
  
  std::ofstream out(("jobs/"+id+".status").c_str());
  out << xml;
}

/*******************************************************************\

Function: get_jobs

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

class job_ordering
{
public:
  bool operator()(const job_statust &j1, const job_statust &j2)
  {
    // SVN revisions rNNNN?
    const std::string &s1=j1.id;
    const std::string &s2=j2.id;
    
    if(s1.size()>=2 && s2.size()>=2 &&
       s1[0]=='r' && s2[0]=='r')
      return atol(s1.substr(1, std::string::npos).c_str())<
             atol(s2.substr(1, std::string::npos).c_str());
    else
    {
      // use date
      struct tm tm1, tm2;
      // Tue Feb 4 12:29:13 2014 +0000
      strptime(j1.date.c_str(), "%a %b %d %T %Y %z", &tm1);
      strptime(j2.date.c_str(), "%a %b %d %T %Y %z", &tm2);
      
      time_t t1=mktime(&tm1);
      time_t t2=mktime(&tm2);

      // secondary criterion      
      if(t1==t2) return s1<s2;
      
      return t1<t2;
    }
  }
};

void get_jobs(std::list<job_statust> &jobs)
{
  // sort into set
  std::set<job_statust, job_ordering> job_set;

  DIR *dir=opendir("jobs");
  if(dir==NULL) return;
  
  std::string suffix=".status";

  struct dirent *ent;
  while((ent=readdir(dir))!=NULL)
  {
    std::string name=ent->d_name;
    if(has_suffix(name, suffix))
    {
      std::string id=name.substr(0, name.size()-suffix.size());
      job_statust job_status(id);
      job_set.insert(job_status);
    }
  }

  closedir(dir);
  
  // dump the set into list
  for(std::set<job_statust>::const_iterator
      s_it=job_set.begin();
      s_it!=job_set.end();
      s_it++)
    jobs.push_back(*s_it);
}
