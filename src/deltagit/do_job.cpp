/*******************************************************************\

Module: Do a jobs for a repository

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iostream>

#include "job_status.h"
#include "do_job.h"

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

  while(job_status.status!=job_statust::DONE)
  {
    switch(job_status.status)
    {
    }
  }

}

