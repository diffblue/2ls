/*******************************************************************\

Module: Summarization

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iostream>

#include <namespace.h>

#include <goto-programs/goto_functions.h>

void transformer(
  const namespacet &ns, 
  const goto_functionst &goto_functions,
  const irep_idt &function_identifier,
  std::ostream &out);
