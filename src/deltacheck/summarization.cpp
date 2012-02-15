/*******************************************************************\

Module: Summarization

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <fstream>
#include "summarization.h"
#include "cgraph_builder.h"
#include "modular_fptr_analysis.h"
//#include "summarize_function_pointers.h"

/*******************************************************************\

Function: summarization

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarization(
  const std::string &file_name,
  const contextt &context,
  const goto_functionst &goto_functions,
  const optionst &options)
{
  /*
  function_pointerst function_pointers;
  
  summarize_function_pointers(context, goto_functions, function_pointers);
   */
  
  cgraph_buildert cg_builder;
  
  cg_builder.add_analysis(new modular_fptr_analysist());
  
  cg_builder.analyze_module(goto_functions);
  cg_builder.serialize(file_name);
}
