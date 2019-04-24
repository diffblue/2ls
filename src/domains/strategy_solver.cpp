/*******************************************************************\

Module: Generic strategy solver

Author: Matej Marusak

\*******************************************************************/

/// \file
/// Generic strategy solver

#include <ssa/ssa_inliner.h>
#include "strategy_solver.h"
#include <goto-symex/adjust_float_expressions.h>

bool strategy_solvert::iterate(invariantt &inv)
{
  bool improved=false;

  domain.solver_iter_init(inv);
  if(domain.has_something_to_solve())
  {
    solver.new_context();

    // Entry value constraints
    exprt pre_expr=domain.to_pre_constraints(inv);
    solver << pre_expr;

    // Exit value constraints
    exprt::operandst strategy_cond_exprs;
    domain.make_not_post_constraints(inv, strategy_cond_exprs);

    domain.strategy_cond_literals.resize(strategy_cond_exprs.size());

    for(std::size_t i=0; i<strategy_cond_exprs.size(); ++i)
    {
      domain.strategy_cond_literals[i]=solver.convert(strategy_cond_exprs[i]);
    }

    exprt cond=disjunction(strategy_cond_exprs);
    adjust_float_expressions(cond, ns);
    solver << cond;

    if(solver()==decision_proceduret::D_SATISFIABLE)
    {
      for(std::size_t row=0; row<domain.strategy_cond_literals.size(); ++row)
      {
        if(solver.l_get(domain.strategy_cond_literals[row]).is_true())
        {
          // Find what values from solver are needed
          std::vector<exprt> required_values=
            domain.get_required_smt_values(row);
          std::vector<exprt> got_values;
          for(auto &c_exprt : required_values)
          {
            got_values.push_back(solver.solver->get(c_exprt));
          }
          domain.set_smt_values(got_values, row);

          find_symbolic_path(loop_guards, domain.get_current_loop_guard(row));

          improved=domain.edit_row(row, inv, improved);
        }
      }
    }
    else
    {
      debug() << "Outer solver: UNSAT!!" << eom;
      improved=domain.handle_unsat(inv, improved);
    }
    solver.pop_context();
    solver << domain.make_permanent(inv);
    domain.post_edit();
  }
  return improved;
}
