/*******************************************************************\

Module: Simplified strategy iteration solver by binary search

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Simplified strategy iteration solver by binary search

#ifdef DEBUG
#include <iostream>
#endif

#include "strategy_solver_binsearch.h"
#include "ssa/local_ssa.h"
#include "util.h"

bool strategy_solver_binsearcht::iterate(invariantt &_inv)
{
  tpolyhedra_domaint::templ_valuet &inv=
    static_cast<tpolyhedra_domaint::templ_valuet &>(_inv);

  bool improved=false;

  solver.new_context(); // for improvement check

  exprt inv_expr=tpolyhedra_domain.to_pre_constraints(inv);

#if 0
  debug() << "improvement check: " << eom;
  debug() << "pre-inv: " << from_expr(ns, "", inv_expr) << eom;
#endif

  solver << inv_expr;

  exprt::operandst strategy_cond_exprs;
  tpolyhedra_domain.make_not_post_constraints(inv, strategy_cond_exprs);

  tpolyhedra_domain.strategy_cond_literals.resize(strategy_cond_exprs.size());

#if 0
  debug() << "post-inv: ";
#endif
  for(std::size_t i=0; i<strategy_cond_exprs.size(); i++)
  {
#if 0
    debug() << (i>0 ? " || " : "") << from_expr(ns, "", strategy_cond_exprs[i]);
#endif
    tpolyhedra_domain.strategy_cond_literals[i]=
      solver.convert(strategy_cond_exprs[i]);
    // solver.set_frozen(tpolyhedra_domain.strategy_cond_literals[i]);
    strategy_cond_exprs[i]=
      literal_exprt(tpolyhedra_domain.strategy_cond_literals[i]);
  }
#if 0
  debug() << eom;
#endif

  solver << disjunction(strategy_cond_exprs);

#if 0
  debug() << "solve(): ";
#endif

  if(solver()==decision_proceduret::resultt::D_SATISFIABLE) // improvement check
  {
#if 0
    debug() << "SAT" << eom;
#endif

#if 0
    for(std::size_t i=0; i<solver.formula.size(); i++)
    {
      debug() << "literal: " << solver.formula[i]
              << " " << solver.l_get(solver.formula[i]) << eom;
    }

    for(std::size_t i=0; i<tpolyhedra_domain.template_size(); i++)
    {
      exprt c=tpolyhedra_domain.get_row_post_constraint(i, inv[i]);
      debug() << "cond: " << from_expr(ns, "", c) << " "
              << from_expr(ns, "", solver.get(c)) << eom;
      debug() << "expr: " << from_expr(
        ns,
        "",
        tpolyhedra_domain.strategy_value_exprs[i]) << " "
              << from_expr(
                ns,
                "",
                simplify_const(
                  solver.get(tpolyhedra_domain.strategy_value_exprs[i])))
              << eom;
      debug() << "guards: "
              << from_expr(ns, "", tpolyhedra_domain.templ[i].pre_guard) << " "
              << from_expr(
                ns, "", solver.get(tpolyhedra_domain.templ[i].pre_guard))
              << eom;
      debug() << "guards: "
              << from_expr(ns, "", tpolyhedra_domain.templ[i].post_guard)
              << " "
              << from_expr(
                ns, "", solver.get(tpolyhedra_domain.templ[i].post_guard))
              << eom;
    }
#endif


    std::size_t row=0;
    for(; row<tpolyhedra_domain.strategy_cond_literals.size(); row++)
    {
      if(solver.l_get(tpolyhedra_domain.strategy_cond_literals[row]).is_true())
        break;  // we've found a row to improve
    }

    debug() << "improving row: " << row << eom;
    std::set<tpolyhedra_domaint::rowt> improve_rows;
    improve_rows.insert(row);

    tpolyhedra_domaint::row_valuet upper=
      tpolyhedra_domain.get_max_row_value(row);
    tpolyhedra_domaint::row_valuet lower=tpolyhedra_domaint::row_valuet(
      simplify_const(
        solver.get(tpolyhedra_domain.strategy_value_exprs[row][0])));

    solver.pop_context();  // improvement check

    solver.new_context(); // symbolic value system

    exprt pre_inv_expr=
      tpolyhedra_domain.to_symb_pre_constraints(inv, improve_rows);

    solver << pre_inv_expr;

    exprt post_inv_expr=tpolyhedra_domain.get_row_symb_post_constraint(row);

    solver << post_inv_expr;

#if 0
    debug() << "symbolic value system: " << eom;
    debug() << "pre-inv: " << from_expr(ns, "", pre_inv_expr) << eom;
    debug() << "post-inv: " << from_expr(ns, "", post_inv_expr) << eom;
#endif

    while(tpolyhedra_domain.less_than(lower, upper))
    {
      tpolyhedra_domaint::row_valuet middle=
        tpolyhedra_domain.between(lower, upper);
      if(!tpolyhedra_domain.less_than(lower, middle))
        middle=upper;

      // row_symb_value >= middle
      exprt c=
        tpolyhedra_domain.get_row_symb_value_constraint(row, middle, true);

#if 0
      debug() << "upper: " << from_expr(ns, "", upper) << eom;
      debug() << "middle: " << from_expr(ns, "", middle) << eom;
      debug() << "lower: " << from_expr(ns, "", lower) << eom;
#endif

      solver.new_context(); // binary search iteration

#if 0
      debug() << "constraint: " << from_expr(ns, "", c) << eom;
#endif

      solver << c;

      if(solver()==decision_proceduret::resultt::D_SATISFIABLE)
      {
#if 0
        debug() << "SAT" << eom;
#endif

#if 0
        for(std::size_t i=0; i<tpolyhedra_domain.template_size(); i++)
        {
          debug() << from_expr(ns, "", tpolyhedra_domain.get_row_symb_value(i))
                  << " " << from_expr(
                    ns, "", solver.get(tpolyhedra_domain.get_row_symb_value(i)))
                  << eom;
        }
#endif

#if 0
        for(const auto &rm : renaming_map)
        {
          debug() << "replace_map (1st): "
                  << from_expr(ns, "", rm.first) << " "
                  << from_expr(ns, "", solver.get(rm.first)) << eom;
          debug() << "replace_map (2nd): "
                  << from_expr(ns, "", rm.second) << " "
                  << from_expr(ns, "", solver.get(rm.second)) << eom;
        }
#endif

        lower=simplify_const(
          solver.get(tpolyhedra_domain.get_row_symb_value(row)));
      }
      else
      {
#if 0
        debug() << "UNSAT" << eom;
#endif

#if 0
        for(std::size_t i=0; i<solver.formula.size(); ++i)
        {
          if(solver.solver->is_in_conflict(solver.formula[i]))
            debug() << "is_in_conflict: " << solver.formula[i] << eom;
          else
            debug() << "not_in_conflict: " << solver.formula[i] << eom;
        }
#endif

        if(!tpolyhedra_domain.less_than(middle, upper))
          middle=lower;
        upper=middle;
      }
      solver.pop_context(); // binary search iteration
    }

    debug() << "update value: " << from_expr(SSA.ns, "", lower) << eom;

    solver.pop_context();  // symbolic value system

    inv[row]=lower;
    improved=true;
  }
  else
  {
#if 0
    debug() << "UNSAT" << eom;
#endif

#ifdef DEBUG_FORMULA
    for(std::size_t i=0; i<solver.formula.size(); ++i)
    {
      if(solver.solver->is_in_conflict(solver.formula[i]))
        debug() << "is_in_conflict: " << solver.formula[i] << eom;
      else
        debug() << "not_in_conflict: " << solver.formula[i] << eom;
    }
#endif

    solver.pop_context(); // improvement check
  }

  return improved;
}
