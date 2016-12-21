#include <iostream>
#include <util/simplify_expr.h>
#include <util/cprover_prefix.h>
#include "ranking_solver_enumeration.h"
#include "util.h"
#include <solvers/smt2/smt2_dec.h>

bool ranking_solver_enumerationt::iterate(invariantt &_rank)
{
  linrank_domaint::templ_valuet &rank=
    static_cast<linrank_domaint::templ_valuet &>(_rank);

  bool improved=false;

  // context for "outer" solver
  solver.new_context();

  // choose round to even rounding mode for template computations
  //  not clear what its implications on soundness and termination of the synthesis are
  exprt rounding_mode=symbol_exprt(CPROVER_PREFIX "rounding_mode", signedbv_typet(32));
  solver << equal_exprt(rounding_mode, from_integer(mp_integer(0), signedbv_typet(32)));

  // handles on values to retrieve from model
  std::vector<linrank_domaint::pre_post_valuest> rank_value_exprs;
  exprt::operandst rank_cond_exprs;
  bvt rank_cond_literals;

  exprt rank_expr=
    linrank_domain.get_not_constraints(rank, rank_cond_exprs, rank_value_exprs);

  solver << rank_expr;

  rank_cond_literals.resize(rank_cond_exprs.size());
  for(unsigned i=0; i<rank_cond_literals.size(); i++)
  {
    rank_cond_literals[i]=solver.solver->convert(rank_cond_exprs[i]);
  }

  debug() << "solve(): ";
  if(solver()==decision_proceduret::D_SATISFIABLE)
  {
    debug() << "SAT" << eom;

    for(unsigned row=0; row<rank_cond_literals.size(); row++)
    {
      // retrieve values from the model x_i and x'_i
      linrank_domaint::pre_post_valuest values;

      if(solver.solver->l_get(rank_cond_literals[row]).is_true())
      {
  for(linrank_domaint::pre_post_valuest::iterator it=
        rank_value_exprs[row].begin();
      it!=rank_value_exprs[row].end(); ++it)
       {
    // model for x_i
   exprt value=solver.solver->get(it->first);
    debug() << "(RANK) Row " << row << " Value for "
      << from_expr(ns, "", it->first)
      << ": " << from_expr(ns, "", value) << eom;
    // model for x'_i
    exprt post_value=solver.solver->get(it->second);
    debug() << "(RANK) Row " << row << " Value for "
      << from_expr(ns, "", it->second)
      << ": " << from_expr(ns, "", post_value) << eom;
    // record all the values
    values.push_back(std::make_pair(value, post_value));
  }

  linrank_domaint::row_valuet symb_values;
  exprt constraint;
  exprt refinement_constraint;

  // generate the new constraint
  constraint=
          linrank_domain.get_row_symb_constraint(symb_values, row,
              values, refinement_constraint);
  simplify_expr(constraint, ns);
  debug() << "Inner Solver: " << row << " constraint "
        << from_expr(ns, "", constraint) << eom;

        inner_solver << equal_exprt(rounding_mode,
            from_integer(mp_integer(0), signedbv_typet(32)));
  inner_solver << constraint;

        // refinement
        if(!refinement_constraint.is_true())
  {
    inner_solver.new_context();
    inner_solver << refinement_constraint;
  }

        // solve
  debug() << "inner solve()" << eom;
  solver_calls++;
  if(inner_solver()==decision_proceduret::D_SATISFIABLE &&
     number_inner_iterations<max_inner_iterations)
  {

    debug() << "inner solver: SAT" << eom;

    std::vector<exprt> c=symb_values.c;

    // new_row_values will contain the new values for c
    linrank_domaint::row_valuet new_row_values;

    // get the model for all c
    for(std::vector<exprt>::iterator it=c.begin(); it!=c.end(); ++it)
    {
      exprt v=inner_solver.solver->get(*it);
      new_row_values.c.push_back(v);
      debug() << "Inner Solver: " << row << " c value for "
        << from_expr(ns, "", *it) << ": "
        << from_expr(ns, "", v)  << eom;
    }
          exprt rmv=inner_solver.solver->get(rounding_mode);
          debug() << "Rounding mode: " << from_expr(ns, "", rmv) << eom;

    // update the current template
    linrank_domain.set_row_value(row, new_row_values, rank);

    improved=true;
  }
  else
  {
    debug() << "inner solver: UNSAT" << eom;

    if(linrank_domain.refine())
    {
      debug() << "refining..." << eom;
      improved=true; // refinement possible
    }
    else
    {
            // no ranking function for the current template
      linrank_domain.set_row_value_to_true(row, rank);
      linrank_domain.reset_refinements();
    }
  }

        if(!refinement_constraint.is_true()) inner_solver.pop_context();
      }
    }

  }
  else
  {
    debug() << "UNSAT" << eom;
    linrank_domain.reset_refinements();
  }

  solver.pop_context();

  return improved;
}
