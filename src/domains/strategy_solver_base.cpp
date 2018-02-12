/*******************************************************************\

Module: Strategy iteration solver base class

Author: Peter Schrammel

\*******************************************************************/

#include "strategy_solver_base.h"

/*******************************************************************\

Function: strategy_solver_baset::find_symbolic_path

  Inputs:

 Outputs:

 Purpose: Find symbolic path that is explored by the current solver
          iteration. A path is specified by a conjunction of literals
          containing loop-select guards of all loops in program.

\*******************************************************************/
void strategy_solver_baset::find_symbolic_path(
  std::set<symbol_exprt> &loop_guards,
  const exprt &current_guard)
{
  for(const symbol_exprt &guard : loop_guards)
  {
    if(guard==current_guard)
    {
      symbolic_path[guard]=true;
      continue;
    }
    exprt guard_value=solver.get(guard);
    if(guard_value.is_true())
      symbolic_path[guard]=true;
    else if(guard_value.is_false())
      symbolic_path[guard]=false;
  }
}
