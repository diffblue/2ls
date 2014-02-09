/*******************************************************************\

Module: Job Status

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cstdlib>
#include <fstream>
#include <set>

#include <dirent.h>

#include <util/xml.h>
#include <util/cout_message.h>
#include <util/suffix.h>

#include <xmllang/xml_parser.h>

#include "git_log.h"
#include "job_status.h"

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
  bool operator()(const std::string &s1, const std::string &s2)
  {
    if(s1.size()>=2 && s2.size()>=2 &&
       s1[0]=='r' && s2[0]=='r')
      return atol(s1.substr(1, std::string::npos).c_str())<
             atol(s2.substr(1, std::string::npos).c_str());
    else
      return s1<s2;
  }
};

void get_jobs(std::list<job_statust> &jobs)
{
  // sort into set
  std::set<std::string, job_ordering> job_set;

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
      job_set.insert(id);
    }
  }

  closedir(dir);
  
  // dump the set into list
  for(std::set<std::string>::const_iterator
      s_it=job_set.begin();
      s_it!=job_set.end();
      s_it++)
    jobs.push_back(job_statust(*s_it));
}
