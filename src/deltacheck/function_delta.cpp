/*******************************************************************\

Module: Delta Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <analyses/goto_check.h>

#include "function_delta.h"

/*******************************************************************\

Function: delta_check

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void function_delta(
  const irep_idt &id,
  const goto_functionst::goto_functiont &f1,
  const goto_functionst::goto_functiont &f2,
  std::ostream &out,
  message_handlert &message_handler)
{
  messaget message(message_handler);

  if(!f2.body.has_assertion())
  {
    message.status("New version has no properties");
    return;
  }

  out << "<h2>Function " << id << "</h2>\n";

  
}

