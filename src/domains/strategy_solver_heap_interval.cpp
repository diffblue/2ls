/*******************************************************************\

Module: Strategy solver for combination of shape and interval domains.

Author: Viktor Malik

\*******************************************************************/

#include "strategy_solver_heap_interval.h"

int strategy_solver_heap_intervalt::unwinding=-1;

/*******************************************************************\

Function: strategy_solver_heap_intervalt::iterate

  Inputs:

 Outputs:

 Purpose: Since template rows for the shape part and the interval part
          are disjoint, we simply call iterate method for each part
          separately

\*******************************************************************/

bool strategy_solver_heap_intervalt::iterate(
  strategy_solver_baset::invariantt &_inv)
{
  heap_interval_domaint::heap_interval_valuet &inv=
    static_cast<heap_interval_domaint::heap_interval_valuet &>(_inv);

  bool heap_improved=unwinding==0 ? heap_solver.iterate(inv.heap_value) : false;
  bool interval_improved=interval_solver.iterate(inv.interval_value);

  return heap_improved || interval_improved;
}

/*******************************************************************\

Function: strategy_solver_heap_intervalt::set_message_handler

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void strategy_solver_heap_intervalt::set_message_handler(
  message_handlert &_message_handler)
{
  heap_solver.set_message_handler(_message_handler);
  interval_solver.set_message_handler(_message_handler);
}
