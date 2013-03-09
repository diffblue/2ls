/*******************************************************************\

Module: Goto Program Preparation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <config.h>

#include <goto-programs/read_goto_binary.h>
#include <goto-programs/goto_inline.h>
#include <goto-programs/link_to_library.h>

#include <analyses/goto_check.h>

#include "get_goto_program.h"

/*******************************************************************\

Function: get_goto_program

  Inputs:

 Outputs:

 Purpose: Phase I: produce a summary for a given file

\*******************************************************************/

void get_goto_program(
  const std::string &file_name,
  const optionst &options,
  symbol_tablet &symbol_table,
  goto_functionst &goto_functions,
  message_handlert &message_handler)
{
  messaget message(message_handler); 
  message.status("Reading goto-program");

  if(read_goto_binary(
       file_name,
       symbol_table, goto_functions, message_handler))
    throw std::string("failed to read goto binary ")+file_name;
    
  config.ansi_c.set_from_symbol_table(symbol_table);

  message.status("Preparing goto-program");

  // finally add the library
  link_to_library(
    symbol_table, goto_functions, message_handler);

  namespacet ns(symbol_table);

  // do partial inlining
  goto_partial_inline(goto_functions, ns, message_handler);
  
  // add checks
  goto_check(ns, options, goto_functions);
  
  // recalculate numbers, etc.
  goto_functions.update();
  
  // add loop ids
  goto_functions.compute_loop_numbers();
}

