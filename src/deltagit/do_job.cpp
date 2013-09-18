/*******************************************************************\

Module: Do a jobs for a repository

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <unistd.h>

#include <cstdlib>
#include <cassert>
#include <iostream>
#include <fstream>

#include <util/prefix.h>
#include <util/tempfile.h>

#include "job_status.h"
#include "do_job.h"

/*******************************************************************\

Function: check_out

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void check_out(job_statust &job_status)
{
  const std::string working_dir=job_status.id+".wd";
  
  // check if we already have it
  if(access((working_dir+"/.git/HEAD").c_str(), R_OK)==0)
  {
    std::cout << "git repository already present\n";
    job_status.next_stage();
    job_status.write();  
    return;
  }

  job_status.status=job_statust::RUNNING;
  job_status.write();

  std::string command;

  // Do a shared clone -- this uses very little disc space.
  // Will overwrite log.
  command="git clone --no-checkout --shared source-repo "+
          working_dir+
          " 2>&1 > "+job_status.id+".log";

  int result1=system(command.c_str());
  if(result1!=0)
  {
    job_status.status=job_statust::FAILURE;
    job_status.write();
    return;
  }
  
  // Now do checkout; this will eat disc space.
  command="cd "+working_dir+"; "+
          "git checkout --detach "+job_status.commit+
          " 2>&1 >> "+job_status.id+".log";

  int result2=system(command.c_str());

  if(result2!=0)
  {
    job_status.status=job_statust::FAILURE;
    job_status.write();
    return;
  }

  job_status.next_stage();
  job_status.write();  
}

/*******************************************************************\

Function: build

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void build(job_statust &job_status)
{
  const std::string working_dir=job_status.id+".wd";
  
  job_status.status=job_statust::RUNNING;
  job_status.write();

  std::string command;

  // Now run build script in working directory.
  command="cd "+working_dir+"; ../build"+
          " 2>&1 >> "+job_status.id+".log";

  int result=system(command.c_str());
  
  if(result!=0)
  {
    job_status.status=job_statust::FAILURE;
    job_status.write();
    return;
  }

  job_status.next_stage();
  job_status.write();  
}

/*******************************************************************\

Function: analyse

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void analyse(
  job_statust &job_status,
  const std::list<job_statust> &jobs)
{
  // get the job before this one

  std::string previous="";

  for(std::list<job_statust>::const_iterator
      j_it=jobs.begin();
      j_it!=jobs.end();
      j_it++)
  {
    if(j_it->id==job_status.id) break;
    previous=j_it->id;
  }
  
  if(previous!="")
  {
    std::cout << "Differential analysis between "
              << previous << " and " << job_status.id
              << "\n";

    // is it built already?
    job_statust old_version(previous);

    if(old_version.stage!=job_statust::ANALYSE)
    {
      std::cout << "Job " << previous << " is not built yet\n";
      return;
    }
  }
  else
    std::cout << "One-version analysis for " << job_status.id
              << "\n";

  job_status.status=job_statust::FAILURE;
}

/*******************************************************************\

Function: do_job

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void do_job(job_statust &job_status,
            const std::list<job_statust> &jobs)
{
  while(job_status.stage!=job_statust::DONE &&
        job_status.status!=job_statust::FAILURE)
  {
    switch(job_status.stage)
    {
    case job_statust::INIT: return; // done by deltagit init
    case job_statust::CHECK_OUT: check_out(job_status); break;
    case job_statust::BUILD: build(job_status); break;
    case job_statust::ANALYSE: analyse(job_status, jobs); break;
    case job_statust::DONE: break;
    }
  }

}

/*******************************************************************\

Function: do_job

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void do_job(const std::string &id)
{
  // get job list
  std::list<job_statust> jobs;
  get_jobs(jobs);

  // get current job status
  job_statust job_status(id);
  do_job(job_status, jobs);
}

/*******************************************************************\

Function: do_job

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void do_job()
{
  // get job list
  std::list<job_statust> jobs;
  get_jobs(jobs);
  
  // Do a job that need work,
  // starting from the end of the log.
  for(std::list<job_statust>::reverse_iterator
      j_it=jobs.rbegin();
      j_it!=jobs.rend();
      j_it++)
  {
    if(j_it->stage!=job_statust::DONE &&
       j_it->stage!=job_statust::INIT &&
       j_it->status!=job_statust::FAILURE)
    {
      std::cout << "Job " << j_it->id << std::endl;
      do_job(*j_it, jobs);
    }
  }
}

