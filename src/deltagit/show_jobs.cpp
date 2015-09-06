/*******************************************************************\

Module: Show the jobs for a repository

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/tempfile.h>
#include <util/prefix.h>

#include "show_jobs.h"
#include "job_status.h"

/*******************************************************************\

Function: show_jobs

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void show_jobs(std::ostream &out)
{
  std::list<job_statust> jobs;
  
  get_jobs(jobs);
  
  for(std::list<job_statust>::const_iterator
      j_it=jobs.begin();
      j_it!=jobs.end();
      j_it++)
  {
    out << j_it->id;

    out << " " << as_string(j_it->stage)
        << " " << as_string(j_it->status);
    
    if(j_it->hostname!="")
      out << " on " << j_it->hostname;
    
    out << "\n";
  }
}
