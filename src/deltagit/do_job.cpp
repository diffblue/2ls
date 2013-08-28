/*******************************************************************\

Module: Do a jobs for a repository

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

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
  
}

/*******************************************************************\

Function: build

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void build(job_statust &job_status)
{
  
}

/*******************************************************************\

Function: analyse

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void analyse(job_statust &job_status)
{
  
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

