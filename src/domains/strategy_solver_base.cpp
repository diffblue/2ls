/*******************************************************************\

Module: Strategy iteration solver base class

Author: Peter Schrammel

\*******************************************************************/

#include "strategy_solver_base.h"

void strategy_solver_baset::find_symbolic_path(
  std::set<symbol_exprt> &loop_guards,
  const exprt &filter_guard)
{
  exprt::operandst path;
  for(const exprt &guard : loop_guards)
  {
    if(guard==filter_guard)
      continue;

    exprt guard_value=solver.get(guard);
    if(guard_value.is_true())
      path.push_back(guard);
    else if(guard_value.is_false())
      path.push_back(not_exprt(guard));
  }
  symbolic_path=conjunction(path);
}
