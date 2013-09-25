/*******************************************************************\

Module: Initialize Jobs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iostream>
#include <fstream>
#include <cstdlib>

#include <util/prefix.h>
#include <util/tempfile.h>

#include "job_status.h"
#include "init.h"
#include "git_log.h"

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
    job_status.status=job_statust::FAILURE;
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
    else if(has_prefix(line, "Date:   "))
    {
      job_status.date=line.substr(8, std::string::npos);
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

  job_status.next_stage();
  job_status.write();  
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

Function: init

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void init(unsigned max_jobs)
{
  // get jobs from git log
  std::list<job_statust> jobs;

  std::cout << "Getting git log\n";

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
  
  unsigned total=0;
  
  // Do jobs that need to be initialized,
  // starting from the end.
  for(std::list<job_statust>::reverse_iterator
      j_it=jobs.rbegin();
      j_it!=jobs.rend();
      j_it++)
  {
    if(max_jobs!=0 && total>=max_jobs)
      break;
    
    if(j_it->stage==job_statust::INIT &&
       j_it->status!=job_statust::FAILURE)
    {
      std::cout << "Setting up job " << j_it->id << "\n";
      std::cout << std::flush;
      init(*j_it);
      total++;
    }
  }
  
  std::cout << "Added " << total << " jobs\n";
}

