/*******************************************************************\

Module: Summarization

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <fstream>

#include "summarization.h"
#include "cgraph_builder.h"
#include "modular_fptr_analysis.h"
#include "modular_globals_analysis.h"

/*******************************************************************\

Function: summarization

  Inputs:

 Outputs:

 Purpose: Phase I: produce a summary for a given file

\*******************************************************************/

void summarization(
  const std::string &file_name,
  const contextt &context,
  const goto_functionst &goto_functions,
  const optionst &options)
{
  #if 0
  cgraph_buildert cg_builder;
  modular_fptr_analysist fptr_analysis;
  modular_globals_analysist globals_analysis;
  
  cg_builder.add_analysis(&fptr_analysis);
  cg_builder.add_analysis(&globals_analysis);
  
  cg_builder.analyze_module(context, goto_functions);
  cg_builder.serialize(file_name);
  #endif

  // do this for each function
  forall_goto_functions(f_it, goto_functions)
  {
  }  
}
