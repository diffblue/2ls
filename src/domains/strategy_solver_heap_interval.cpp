/**
 *  Viktor Malik, 3/30/17 (c).
 */

#include "strategy_solver_heap_interval.h"

bool
strategy_solver_heap_intervalt::iterate(strategy_solver_baset::invariantt &_inv)
{
  heap_interval_domaint::heap_interval_valuet &inv=
    static_cast<heap_interval_domaint::heap_interval_valuet &>(_inv);

  bool heap_improved=heap_solver.iterate(inv.heap_value);
  bool interval_improved=interval_solver.iterate(inv.interval_value);

  return heap_improved || interval_improved;
}

void strategy_solver_heap_intervalt::set_message_handler(
  message_handlert &_message_handler)
{
  heap_solver.set_message_handler(_message_handler);
  interval_solver.set_message_handler(_message_handler);
}
