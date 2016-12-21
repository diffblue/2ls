/*******************************************************************\

Module: Abstract domain base class

Author: Peter Schrammel

\*******************************************************************/

#ifdef DEBUG
#include <iostream>
#endif

#include <util/simplify_expr.h>
#include <util/cprover_prefix.h>

#include "lexlinrank_solver_enumeration.h"
#include "util.h"

// #define DEBUG_OUTER_FORMULA
// #define DEBUG_INNER_FORMULA

/*******************************************************************\

Function: lexlinrank_solver_enumerationt::iterate

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool lexlinrank_solver_enumerationt::iterate(invariantt &_rank)
{
  lexlinrank_domaint::templ_valuet &rank=
    static_cast<lexlinrank_domaint::templ_valuet &>(_rank);

  bool improved=false;
  static std::vector<unsigned> number_elements_per_row;
  number_elements_per_row.resize(rank.size());

  debug() << "(RANK) no rows=" << rank.size() << eom;

  solver.new_context();


  // choose round to even rounding mode for template computations
  // not clear what its implications on soundness and
  // termination of the synthesis are
  exprt rounding_mode=
    symbol_exprt(CPROVER_PREFIX "rounding_mode", signedbv_typet(32));
  solver << equal_exprt(
    rounding_mode, from_integer(mp_integer(0), signedbv_typet(32)));

  // handles on values to retrieve from model
  std::vector<lexlinrank_domaint::pre_post_valuest> rank_value_exprs;
  exprt::operandst rank_cond_exprs;
  bvt rank_cond_literals;

  exprt rank_expr=
    lexlinrank_domain.get_not_constraints(
      rank,
      rank_cond_exprs,
      rank_value_exprs);

  solver << rank_expr;

  rank_cond_literals.resize(rank_cond_exprs.size());
  for(std::size_t i=0; i<rank_cond_exprs.size(); i++)
  {
    rank_cond_literals[i]=solver.solver->convert(rank_cond_exprs[i]);
  }

  debug() << "Outer solve(): ";

#if 0
  // check whether the literal is UNSAT to start with
  satcheck_minisat_no_simplifiert test_satcheck;
  bv_pointerst test_solver=bv_pointerst(ns, test_satcheck);

  test_solver << rank_expr;

  if(test_solver()==decision_proceduret::D_SATISFIABLE)
    debug() << "test solver: SAT" << eom;
  else
    debug() << "test solver: UNSAT" << eom;
#endif

  if(solver()==decision_proceduret::D_SATISFIABLE)
  {
    debug() << "Outer solver: SAT" << eom;

    for(std::size_t row=0; row<rank_cond_literals.size(); row++)
    {
      // retrieve values from the model x_i and x'_i
      lexlinrank_domaint::pre_post_valuest values;

      if(solver.solver->l_get(rank_cond_literals[row]).is_true())
      {
        for(auto &row_expr : rank_value_exprs[row])
        {
          // model for x_i
          exprt value=solver.solver->get(row_expr.first);
          debug() << "Row " << row << " Value for "
                  << from_expr(ns, "", row_expr.first)
                  << ": " << from_expr(ns, "", value) << eom;
          // model for x'_i
          exprt post_value=solver.solver->get(row_expr.second);
          debug() << "Row " << row << " Value for "
                  << from_expr(ns, "", row_expr.second)
                  << ": " << from_expr(ns, "", post_value) << eom;
          // record all the values
          values.push_back(std::make_pair(value, post_value));
        }

        lexlinrank_domaint::row_valuet symb_values;
        symb_values.resize(rank[row].size());

        // debug() << "elements: " << rank[row].size() << eom;

        exprt constraint;
        exprt refinement_constraint;

        // generate the new constraint
        constraint=lexlinrank_domain.get_row_symb_constraint(
          symb_values,
          row, values,
          refinement_constraint);

        simplify_expr(constraint, ns);
        debug() << "Constraint sent to the inner solver: " << row
                << " constraint ";
        pretty_print_termination_argument(debug(), ns, constraint);
        debug() << eom;

        *inner_solver << constraint;

        // set rounding mode
        *inner_solver << equal_exprt(
          rounding_mode, from_integer(mp_integer(0), signedbv_typet(32)));

        // refinement
        if(!refinement_constraint.is_true())
        {
          inner_solver->new_context();
          *inner_solver << refinement_constraint;
        }

        debug() << "Inner solve()" << eom;
        // solve
        solver_calls++;
        bool inner_solver_result=(*inner_solver)();
        if(inner_solver_result==decision_proceduret::D_SATISFIABLE &&
           number_inner_iterations<max_inner_iterations)
        {
          number_inner_iterations++;

          debug() << "Inner solver: "
                  << "SAT and the max number of iterations was not reached "
                  << eom;
          debug() << "Inner solver: "
                  << "Current number of iterations="
                  << number_inner_iterations << eom;
          debug() << "Inner solver: "
                  << "Current number of components for row "
                  << row << " is " << number_elements_per_row[row]+1 << eom;

          // new_row_values will contain the new values for c and d
          lexlinrank_domaint::row_valuet new_row_values;
          new_row_values.resize(rank[row].size());

          for(std::size_t constraint_no=0;
              constraint_no<symb_values.size(); ++constraint_no)
          {
            std::vector<exprt> c=symb_values[constraint_no].c;

            // get the model for all c
            for(auto &e : c)
            {
              exprt v=inner_solver->solver->get(e);
              new_row_values[constraint_no].c.push_back(v);
              debug() << "Inner Solver: row " << row
                      << "==> c value for ";
              pretty_print_termination_argument(debug(), ns, e);
              debug() << ": ";
              pretty_print_termination_argument(debug(), ns, v);
              debug() << eom;
            }
          }

          improved=true;

          // update the current template
          lexlinrank_domain.set_row_value(row, new_row_values, rank);

          if(!refinement_constraint.is_true()) inner_solver->pop_context();
        }
        else
        {
          if(inner_solver_result==decision_proceduret::D_UNSATISFIABLE)
            debug() << "Inner solver: UNSAT" << eom;
          else
            debug() << "Inner solver: reached max number of iterations" << eom;

          debug() << "Inner solver: number of iterations="
                  << number_inner_iterations << eom;

#ifdef DEBUG_INNER_FORMULA
          for(std::size_t i=0; i<inner_solver->formula.size(); i++)
          {
            if(inner_solver->solver->is_in_conflict(inner_solver->formula[i]))
              debug() << "is_in_conflict: " << inner_solver->formula[i] << eom;
            else
              debug() << "not_in_conflict: " << inner_solver->formula[i] << eom;
          }
#endif

          if(lexlinrank_domain.refine())
          {
            debug() << "refining..." << eom;
            improved=true; // refinement possible

            if(!refinement_constraint.is_true()) inner_solver->pop_context();
          }
          else
          {
            if(number_elements_per_row[row]==max_elements-1)
            {
              debug() << "Reached the max no of lexicographic components "
                      << "and no ranking function was found" << eom;
              // no ranking function for the current template
              lexlinrank_domain.set_row_value_to_true(row, rank);
              lexlinrank_domain.reset_refinements();
            }
            else
            {
              number_elements_per_row[row]++;
              debug() << "Inner solver: increasing the number "
                      << "of lexicographic components for row " << row
                      << " to " << number_elements_per_row[row]+1 << eom;
              // reset the inner solver
              debug() << "Reset the inner solver " << eom;
              delete inner_solver;
              inner_solver=incremental_solvert::allocate(ns);
              solver_instances++;
              lexlinrank_domain.reset_refinements();

              lexlinrank_domain.add_element(row, rank);
              number_inner_iterations=0;
              debug() << "Inner solver: "
                      << "the number of inner iterations for row " << row
                      << " was reset to " << number_inner_iterations << eom;
              improved=true;
            }
          }
        }
      }
    }
  }
  else
  {
    debug() << "Outer solver: UNSAT!!" << eom;
    lexlinrank_domain.reset_refinements();

#ifdef DEBUG_OUTER_FORMULA
    for(std::size_t i=0; i<solver.formula.size(); i++)
    {
      if(solver.solver->is_in_conflict(solver.formula[i]))
        debug() << "is_in_conflict: " << solver.formula[i] << eom;
      else
        debug() << "not_in_conflict: " << solver.formula[i] << eom;
    }
#endif
  }

  solver.pop_context();
  return improved;
}
