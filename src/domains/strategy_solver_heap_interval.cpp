/*******************************************************************\

Module: Strategy solver for combination of shape and interval domains.

Author: Viktor Malik

\*******************************************************************/

#include "strategy_solver_heap_interval.h"

/*******************************************************************\

Function: strategy_solver_heap_intervalt::iterate

  Inputs:

 Outputs:

 Purpose: Run iteration of each solver separately, but every time
          in the context of the current invariant found by the other
          solver. The interval solving is also restricted to
          a symbolic path found by the heap solver.

\*******************************************************************/

bool strategy_solver_heap_intervalt::iterate(
  strategy_solver_baset::invariantt &_inv)
{
  heap_interval_domaint::heap_interval_valuet &inv=
    static_cast<heap_interval_domaint::heap_interval_valuet &>(_inv);

  // Run one iteration of heap solver in the context of invariant from
  // the interval solver
  solver.new_context();
  solver << heap_interval_domain.interval_domain.to_pre_constraints(
    inv.interval_value);
  bool heap_improved=heap_solver.iterate(inv.heap_value);
  solver.pop_context();

  if(heap_improved)
  {
    // If heap part was improved, restrict interval part to found symbolic path
    symbolic_path=heap_solver.symbolic_path;
    heap_interval_domain.interval_domain.restrict_to_sympath(symbolic_path);
  }

  // Run one interation of interval solver in the context of invariant from
  // the heap solver
  solver.new_context();
  solver << heap_interval_domain.heap_domain.to_pre_constraints(inv.heap_value);
  bool interval_improved=interval_solver.iterate(inv.interval_value);
  solver.pop_context();

  if(heap_improved)
    heap_interval_domain.interval_domain.undo_restriction();

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
