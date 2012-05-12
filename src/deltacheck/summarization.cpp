/*******************************************************************\

Module: Summarization

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <fstream>

#include <config.h>

#include <goto-programs/goto_inline.h>
#include <goto-programs/read_goto_binary.h>
#include <goto-programs/link_to_library.h>

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

/*******************************************************************\

Function: summarization

  Inputs:

 Outputs:

 Purpose: Phase I: produce a summary for a given file

\*******************************************************************/

void summarization(
  const std::string &file_name,
  const optionst &options,
  message_handlert &message_handler)
{
  // get the goto program
  contextt context;
  goto_functionst goto_functions;

  if(read_goto_binary(
       file_name,
       context, goto_functions, message_handler))
    throw std::string("failed to read goto binary ")+file_name;
    
  config.ansi_c.set_from_context(context);

  // finally add the library
  link_to_library(
    context, goto_functions, options, message_handler);

  namespacet ns(context);

  // do partial inlining
  goto_partial_inline(goto_functions, ns, message_handler);
  
  // recalculate numbers, etc.
  goto_functions.update();

  // add loop ids
  goto_functions.compute_loop_numbers();
  
  std::string summary_file_name=file_name+".summary";
  std::ofstream summary_file(summary_file_name.c_str(),
    std::ios::binary|std::ios::trunc|std::ios::out);
  
  if(!summary_file)
    throw std::string("failed to write summary file");

  ::summarization(context, goto_functions, options);
}

