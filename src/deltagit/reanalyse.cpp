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
    if(j_it->stage==job_statust::DONE)
    {
      std::cout << "Reanalysing job " << j_it->id << "\n";
      j_it->status=job_statust::WAITING;
      j_it->stage=job_statust::ANALYSE;
      j_it->write();
    }
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

  if(job_status.stage==job_statust::DONE)
  {
    std::cout << "Reanalysing job " << job_status.id << "\n";
    job_status.status=job_statust::WAITING;
    job_status.stage=job_statust::ANALYSE;
    job_status.write();
  }
}

