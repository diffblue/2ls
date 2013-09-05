/*******************************************************************\

Module: Initialize Jobs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iostream>
#include <fstream>

#include <util/prefix.h>
#include <util/tempfile.h>

#include "job_status.h"
#include "init.h"

/*******************************************************************\

Function: init

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void init(job_statust &job_status)
{
  std::string command;
  temporary_filet tempfile("deltagit", "txt");

  // do a git show to learn more about the job
  command="cd source-repo; git show "+job_status.commit+
          " --numstat"+
          " > "+tempfile();

  int result1=system(command.c_str());
  if(result1!=0)
  {
    job_status.failure=true;
    // don't write, commit might be bogus
    return;
  }

  // parse the file
  std::ifstream in(tempfile().c_str());
  if(!in) return;
  
  std::string line;
  
  job_status.added=0;
  job_status.deleted=0;
  job_status.message="";
  
  while(std::getline(in, line))
  {
    if(has_prefix(line, "    git-svn-id: "))
    {
    }
    else if(has_prefix(line, "    "))
    {
      // commit message
      job_status.message+=line.substr(4, std::string::npos)+"\n";      
    }
    else if(has_prefix(line, "Author: "))
    {
      job_status.author=line.substr(8, std::string::npos);
    }
    else if(!line.empty() && isdigit(line[0]))
    {
      // <num-added>\t<num-deleted>\t<file-name>
      const std::size_t end_added=line.find('\t', 0);
      if(end_added==std::string::npos) continue;
      const std::size_t end_deleted=line.find('\t', end_added+1);
      if(end_deleted==std::string::npos) continue;
      
      job_status.added+=atol(line.substr(0, end_added).c_str());
      job_status.deleted+=atol(line.substr(end_added+1, end_deleted-end_added-1).c_str());
    }
  }       
  
  // strip trailing \n from commit message
  std::string &message=job_status.message;
  while(!message.empty() && message[message.size()-1]=='\n')
    message.resize(message.size()-1);
  
  job_status.status=job_statust::CHECK_OUT;
  job_status.write();  
}

/*******************************************************************\

Function: init

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void init()
{
  // get job list
  std::list<job_statust> jobs;
  get_jobs(jobs);
  
  // do jobs that need to be initialized
  for(std::list<job_statust>::iterator
      j_it=jobs.begin();
      j_it!=jobs.end();
      j_it++)
  {
    if(j_it->status==job_statust::INIT &&
       !j_it->failure)
    {
      std::cout << "Setting up job " << j_it->id << std::endl;
      init(*j_it);
    }
  }
}

