/*******************************************************************\

Module: Show the overview for a repository

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <fstream>

#include "../html/html_escape.h"

#include "report.h"
#include "job_status.h"
#include "deltagit_config.h"

/*******************************************************************\

Function: report

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void report()
{
  deltagit_configt deltagit_config;
  
  std::ofstream out("index.html");
  
  std::string title="DeltaCheck Report";
  if(deltagit_config.description!="")
    title+=" "+deltagit_config.description;
  
  std::list<job_statust> jobs;

  get_jobs(jobs);
  
  for(std::list<job_statust>::const_iterator
      j_it=jobs.begin();
      j_it!=jobs.end();
      j_it++)
  {
    out << j_it->id;

    out << " " << as_string(j_it->status);
    if(j_it->failure) out << " FAILED";
    
    out << "\n";
  }
  
  out << "<html>\n"
         "<head>\n"
         "<title>";
  out << html_escape(title) << "</title>\n";
  
  out << "<body>\n";
  
  
  
  out << "</body>\n";
  out << "</html>\n";
}
