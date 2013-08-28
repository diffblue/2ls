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
    status=NEW;
    return;
  }

  if(src.name!="deltagit_jobstatus")
    throw std::string("unexpected XML for job status");

  const std::string status_string=src.get_attribute("status");
  
  if(status_string=="new")
    status=NEW;
  else if(status_string=="checked_out")
    status=CHECKED_OUT;
  else if(status_string=="built")
    status=BUILT;
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
  case job_statust::NEW: return "new";
  case job_statust::CHECKED_OUT: return "checked_out";
  case job_statust::BUILT: return "built";
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
