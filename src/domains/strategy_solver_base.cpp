/*******************************************************************\

Module: Strategy iteration solver base class

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Strategy iteration solver base class

#include "strategy_solver_base.h"

/// Find symbolic path that is explored by the current solver iteration. A path
/// is specified by a conjunction of literals containing loop-select guards of
/// all loops in program.
void strategy_solver_baset::find_symbolic_path(
  std::set<std::pair<symbol_exprt, symbol_exprt>> &loop_guards,
  const exprt &current_guard)
{
  for(const auto &guard : loop_guards)
  {
    if(guard.first==current_guard)
    {
      symbolic_path[guard.first]=true;
      continue;
    }
    exprt ls_guard_value=solver.get(guard.first);
    exprt lh_guard_value=solver.get(guard.second);
    if(ls_guard_value.is_true() && lh_guard_value.is_true())
      symbolic_path[guard.first]=true;
    else if(ls_guard_value.is_false())
      symbolic_path[guard.first]=false;
  }
}

/// Function for printing out the value assigned to an expression and to all its
/// subexpressions by the SMT solver.
void strategy_solver_baset::debug_smt_model(
  const exprt &expr,
  const namespacet &ns)
{
  std::cerr << from_expr(ns, "", expr) << ": "
            << from_expr(ns, "", solver.solver->get(expr)) << "\n";
  forall_operands(op, expr)
  {
    debug_smt_model(*op, ns);
  }
}
