/*******************************************************************\

Module: Delta Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_FUNCTION_DELTA_H
#define CPROVER_FUNCTION_DELTA_H

#include <ostream>

#include <util/message.h>
#include <goto-programs/goto_functions.h>

void function_delta(
  const irep_idt &id,
  const goto_functionst::goto_functiont &f1,
  const goto_functionst::goto_functiont &f2,
  std::ostream &,
  message_handlert &);

#endif
