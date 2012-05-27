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
  const goto_functionst::goto_functiont &goto_function,
  std::ostream &out);
