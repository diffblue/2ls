/*******************************************************************\

Module: Goto Program Preparation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <symbol_table.h>
#include <message.h>
#include <options.h>

#include <goto-programs/goto_functions.h>

void get_goto_program(
  const std::string &file_name,
  const optionst &options,
  symbol_tablet &symbol_table,
  goto_functionst &goto_functions,
  message_handlert &message_handler);
