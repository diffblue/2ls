/*******************************************************************\

Module: Goto Program Preparation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <context.h>
#include <message.h>
#include <options.h>

#include <goto-programs/goto_functions.h>

void get_goto_program(
  const std::string &file_name,
  const optionst &options,
  contextt &context,
  goto_functionst &goto_functions,
  message_handlert &message_handler);
