/*******************************************************************\

Module: Do a jobs for a repository

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cstdlib>
#include <cassert>
#include <iostream>

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
  std::string working_dir=job_status.id+".wd";

  std::string command;

  // do a shared clone -- this uses very little disc space
  command="git clone --no-checkout --shared source-repo "+
          working_dir;

  int result1=system(command.c_str());
  if(result1!=0)
  {
    job_status.failure=true;
    job_status.write();
    return;
  }
  
  // now do checkout; this will eat disc space
  command="cd "+working_dir+"; "+
          "git checkout --detach "+job_status.commit;
  int result2=system(command.c_str());

  if(result2!=0)
  {
    job_status.failure=true;
    job_status.write();
    return;
  }

  job_status.status=job_statust::BUILD;
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
  job_status.failure=true;
}

/*******************************************************************\

Function: analyse

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void analyse(job_statust &job_status)
{
  job_status.failure=true;
}

/*******************************************************************\

Function: do_job

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void do_job(job_statust &job_status)
{
  while(job_status.status!=job_statust::DONE &&
        !job_status.failure)
  {
    switch(job_status.status)
    {
    case job_statust::CHECK_OUT: check_out(job_status); break;
    case job_statust::BUILD: build(job_status); break;
    case job_statust::ANALYSE: analyse(job_status); break;
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
  // get current job status
  job_statust job_status(id);
  do_job(job_status);
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
  
  // do jobs that need work
  for(std::list<job_statust>::iterator
      j_it=jobs.begin();
      j_it!=jobs.end();
      j_it++)
  {
    if(j_it->status!=job_statust::DONE &&
       !j_it->failure)
    {
      std::cout << "Job " << j_it->id << std::endl;
      do_job(*j_it);
    }
  }
}

