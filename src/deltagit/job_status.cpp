/*******************************************************************\

Module: Job Status

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <fstream>

#include <util/xml.h>
#include <util/cout_message.h>

#include <xmllang/xml_parser.h>

#include "git_log.h"
#include "job_status.h"

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
      
  if(parse_xml(id+".status", message_handler, src))
  {
    // assume it's new
    status=CHECK_OUT;
    failure=false;
    return;
  }

  if(src.name!="deltagit_jobstatus")
    throw std::string("unexpected XML for job status");

  const std::string status_string=src.get_attribute("status");
  
  if(status_string=="check out")
    status=CHECK_OUT;
  else if(status_string=="build")
    status=BUILD;
  else if(status_string=="analyse")
    status=ANALYSE;
  else if(status_string=="done")
    status=DONE;
  else
    throw std::string("unexpected status");

  if(src.get_attribute("failure")=="1")
    failure=true;
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
  case job_statust::CHECK_OUT: return "check out";
  case job_statust::BUILD: return "build";
  case job_statust::ANALYSE: return "analyse";
  case job_statust::DONE: return "done";
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
  
  if(failure)
    xml.set_attribute("failure", "1");
  
  std::ofstream out((id+".status").c_str());
  out << xml;
}

/*******************************************************************\

Function: get_extension

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string get_extension(const std::string &s)
{
  std::size_t pos=s.rfind('.');
  if(pos==std::string::npos) return "";
  return s.substr(pos+1, std::string::npos);
}

/*******************************************************************\

Function: get_file

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string get_file(const std::string &s)
{
  std::size_t pos=s.rfind('/');
  if(pos==std::string::npos) return s;
  return s.substr(pos+1, std::string::npos);
}

/*******************************************************************\

Function: get_jobs

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void get_jobs(std::list<job_statust> &jobs)
{
  // get the git log
  git_logt git_log;
  
  // rummage through it, looking for 'interesting' commits
  // we reverse, to start with older commits
  for(git_logt::entriest::const_reverse_iterator
      l_it=git_log.entries.rbegin();
      l_it!=git_log.entries.rend();
      l_it++)
  {
    bool found=false;
  
    for(std::list<std::string>::const_iterator
        f_it=l_it->files.begin();
        f_it!=l_it->files.end();
        f_it++)
    {
      std::string file=get_file(*f_it);
      std::string ext=get_extension(file);

      if(ext=="c" || ext=="C" ||
         ext=="cpp" || ext=="c++" ||
         ext=="h" || ext=="hpp")
      {
        found=true;
        break;
      }    
    }

    if(found)
    {
      std::string id;

      if(l_it->git_svn_id!="")
        id="r"+l_it->git_svn_id;
      else
        id=l_it->commit;
      
      job_statust job_status(id);
      job_status.commit=l_it->commit;
      
      jobs.push_back(job_status);
    }
  }
}
