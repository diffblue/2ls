/*******************************************************************\

Module: Summarizer

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "../ssa/local_ssa.h"

#include "summarizer.h"

/*******************************************************************\

Function: summarizert::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

summarizert::resultt summarizert::operator()(
  const goto_functionst &goto_functions)
{
  // get the entry point
  const goto_functionst::function_mapt::const_iterator
    f_it=goto_functions.function_map.find(goto_functions.entry_point());
    
  if(f_it==goto_functions.function_map.end())
    throw "Failed to find entry point, please complete linking.";

  // build SSA
  
  local_SSAt local_SSA(f_it->second, ns);
  
  
}

/*******************************************************************\

Function: summarizert::report_statistics()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarizert::report_statistics()
{
}
  
/*******************************************************************\

Function: summarizert::initialize_property_map

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarizert::initialize_property_map(
  const goto_functionst &goto_functions)
{

}
