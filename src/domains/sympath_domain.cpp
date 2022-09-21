/*******************************************************************\

Module: Abstract domain for computing invariants for different
        program symbolic paths

Author: Viktor Malik

\*******************************************************************/

/// \file
/// Abstract domain for computing invariants for different program symbolic
/// paths. The invariants can be computed in arbitrary domain (called the inner
/// domain).
/// Designed to work with strategy_solver_sympatht.

#include "sympath_domain.h"
#include "strategy_solver_sympath.h"

void sympath_domaint::output_value(
  std::ostream &out,
  const domaint::valuet &value,
  const namespacet &ns) const
{
  auto &v=dynamic_cast<const sympath_valuet &>(value);
  for(auto &config : v)
  {
    out << from_expr(ns, "", config.first) << "==>\n";
    inner_domain->output_value(out, *config.second, ns);
  }
}

void sympath_domaint::output_domain(
  std::ostream &out,
  const namespacet &ns) const
{
  inner_domain->output_domain(out, ns);
}

/// Project onto a set of variables. The result invariant is a disjunction of
/// expressions:
///   sympath_expr && sympath_inv
/// where sympath_expr is the formula representing the symbolic path and
///       sympath_inv  is the invariant computed for the given symbolic path.
void sympath_domaint::project_on_vars(domaint::valuet &value,
                                      const var_sett &vars,
                                      exprt &result,
                                      bool ignore_top)
{
  auto &v=dynamic_cast<sympath_valuet &>(value);
  exprt::operandst c;
  for(auto &config : v)
  {
    exprt config_result;
    inner_domain->project_on_vars(
      *config.second, vars, config_result, ignore_top);
    c.push_back(and_exprt(config.first, config_result));
  }
  c.push_back(no_loops_path);

  result=c.empty() ? true_exprt() : disjunction(c);
}

std::unique_ptr<strategy_solver_baset> sympath_domaint::new_strategy_solver(
  incremental_solvert &solver,
  const local_SSAt &SSA,
  message_handlert &message_handler)
{
  auto inner_solver=inner_domain->new_strategy_solver(
    solver, SSA, message_handler);
  return std::unique_ptr<strategy_solver_baset>(
    new strategy_solver_sympatht(
      *this, std::move(inner_solver), solver, SSA, message_handler));
}
