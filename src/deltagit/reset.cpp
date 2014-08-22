/*******************************************************************\

Module: Reset Jobs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iostream>

#include "job_status.h"
#include "reset.h"

/*******************************************************************\

Function: reset

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void reset()
{
  // get job list
  std::list<job_statust> jobs;
  get_jobs(jobs);
  
  // reset jobs that need to be
  for(std::list<job_statust>::iterator
      j_it=jobs.begin();
      j_it!=jobs.end();
      j_it++)
  {
    if(j_it->status==job_statust::FAILURE)
    {
      std::cout << "Resetting job " << j_it->id << "\n";
      j_it->status=job_statust::WAITING;
      j_it->write();
    }
  }
}

/*******************************************************************\

Function: reset

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void reset(const std::string &job)
{
  job_statust job_status(job);

  if(job_status.status==job_statust::FAILURE)
  {
    std::cout << "Resetting job " << job_status.id << "\n";
    job_status.status=job_statust::WAITING;
    job_status.write();
  }
}

