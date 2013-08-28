/*******************************************************************\

Module: Job Status

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/xml.h>
#include <util/cout_message.h>

#include <xmllang/xml_parser.h>

#include "job_status.h"

/*******************************************************************\

Function: job_statust::read

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void job_statust::read()
{
  xmlt src;
  
  console_message_handlert message_handler;
      
  if(parse_xml("", message_handler, src))
  {
    // assume it's new
    status=CHECK_OUT;
    failure=false;
    return;
  }

  if(src.name!="deltagit_jobstatus")
    throw std::string("unexpected XML for job status");

  const std::string status_string=src.get_attribute("status");
  
  if(status_string=="check out")
    status=CHECK_OUT;
  else if(status_string=="build")
    status=BUILD;
  else if(status_string=="analyse")
    status=ANALYSE;
  else if(status_string=="done")
    status=DONE;
  else
    throw std::string("unexpected status");
}

/*******************************************************************\

Function: as_string

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string as_string(job_statust::statust status)
{
  switch(status)
  {
  case job_statust::CHECK_OUT: return "check out";
  case job_statust::BUILD: return "build";
  case job_statust::ANALYSE: return "analyse";
  case job_statust::DONE: return "done";
  default: return "";
  }
}

/*******************************************************************\

Function: job_statust::write

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void job_statust::write()
{
  xmlt dest;
  dest.name="deltagit_jobstatus";

  dest.set_attribute("id", id);
  dest.set_attribute("status", as_string(status));
}
