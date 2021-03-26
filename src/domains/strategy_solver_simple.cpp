/*******************************************************************\

Module: Generic strategy solver

Author: Matej Marusak

\*******************************************************************/

/// \file
/// Generic strategy solver

#include <ssa/ssa_inliner.h>
#include "strategy_solver_simple.h"
#include <goto-symex/adjust_float_expressions.h>

bool strategy_solver_simplet::iterate(invariantt &_inv)
{
  auto &inv=dynamic_cast<simple_domaint::valuet &>(_inv);

  bool improved=false;

  domain.init_value_solver_iteration(inv);
  if(domain.has_something_to_solve())
  {
    solver.new_context();
    domain.strategy_value_exprs.clear();

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
    adjust_float_expressions(cond, SSA.ns);
    solver << cond;

    if(solver()==decision_proceduret::resultt::D_SATISFIABLE)
    {
#ifdef DEBUG
      std::cerr << "Pre-condition:\n";
      debug_smt_model(pre_expr, ns);
      std::cerr << "Post-condition:\n";
      debug_smt_model(cond, ns);
#endif
      for(std::size_t row=0; row<domain.strategy_cond_literals.size(); ++row)
      {
        if(solver.l_get(domain.strategy_cond_literals[row]).is_true())
        {
          // Retrieve values of domain strategy expressions from the model
          // and store them into smt_model_values.
          if(domain.strategy_value_exprs.size()>row)
          {
            domain.smt_model_values.clear();
            for(auto &c_exprt : domain.strategy_value_exprs[row])
            {
              domain.smt_model_values.push_back(solver.solver->get(c_exprt));
            }
          }

          if(with_sympaths)
            find_symbolic_path(loop_guards, domain.get_current_loop_guard(row));

          improved=domain.edit_row(row, inv, improved);
        }
      }
    }
    else
    {
#ifdef DEBUG
      debug() << "Outer solver: UNSAT!!" << eom;
#endif
      improved=domain.handle_unsat(inv, improved);
    }
    solver.pop_context();
    solver << domain.get_permanent_expr(inv);
    domain.finalize_solver_iteration();
  }
  return improved;
}
