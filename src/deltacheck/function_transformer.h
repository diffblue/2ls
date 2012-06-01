/*******************************************************************\

Module: Summarization

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iostream>

#include <namespace.h>
#include <message.h>

#include <goto-programs/goto_functions.h>

void function_transformer(
  const namespacet &ns, 
  const goto_functionst &goto_functions,
  const goto_functionst::goto_functiont &goto_function,
  message_handlert &message_handler,
  std::ostream &out);
