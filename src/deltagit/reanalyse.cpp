/*******************************************************************\

Module: Reanalyse Jobs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iostream>

#include "job_status.h"
#include "reanalyse.h"

/*******************************************************************\

Function: reanalyse

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void reanalyse(job_statust &job_status)
{
  if(job_status.stage==job_statust::DONE)
  {
    std::cout << "Reanalysing job " << job_status.id << "\n";
    job_status.status=job_statust::WAITING;
    job_status.stage=job_statust::ANALYSE;
    job_status.write();
  }
  else if(job_status.stage==job_statust::ANALYSE &&
          job_status.status==job_statust::FAILURE)
  {
    std::cout << "Resetting job " << job_status.id << "\n";
    job_status.status=job_statust::WAITING;
    job_status.stage=job_statust::ANALYSE;
    job_status.write();
  }
}

/*******************************************************************\

Function: reanalyse

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void reanalyse()
{
  // get job list
  std::list<job_statust> jobs;
  get_jobs(jobs);
  
  // reanalyse jobs that need to be
  for(std::list<job_statust>::iterator
      j_it=jobs.begin();
      j_it!=jobs.end();
      j_it++)
  {
    reanalyse(*j_it);
  }
}

/*******************************************************************\

Function: reanalyse

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void reanalyse(const std::string &job)
{
  job_statust job_status(job);
  reanalyse(job_status);
}

