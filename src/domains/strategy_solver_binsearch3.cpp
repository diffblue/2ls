/*******************************************************************\

Module: Full strategy iteration solver by binary search

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Full strategy iteration solver by binary search

#ifdef DEBUG
#include <iostream>
#endif

#include <cassert>

#include "strategy_solver_binsearch3.h"
#include "util.h"

#define SUM_BOUND_VAR "sum_bound#"

bool strategy_solver_binsearch3t::iterate(invariantt &_inv)
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
    strategy_cond_exprs[i]=
        literal_exprt(tpolyhedra_domain.strategy_cond_literals[i]);
  }
  debug() << eom;

  solver << disjunction(strategy_cond_exprs);

#if 0
  debug() << "solve(): ";
#endif

  std::set<tpolyhedra_domaint::rowt> improve_rows;
  std::map<tpolyhedra_domaint::rowt, symbol_exprt> symb_values;
  std::map<tpolyhedra_domaint::rowt, constant_exprt> lower_values;
  exprt::operandst blocking_constraint;
  bool improved_from_neginf=false;
  while(solver()==decision_proceduret::D_SATISFIABLE) // improvement check
  {
#if 0
    debug() << "SAT" << eom;
#endif
    improved=true;

    std::size_t row=0;
    for(; row<tpolyhedra_domain.strategy_cond_literals.size(); row++)
    {
      if(solver.l_get(tpolyhedra_domain.strategy_cond_literals[row]).is_true())
      {
#if 1
        debug() << "improve row " << row  << eom;
#endif
        improve_rows.insert(row);
        symb_values[row]=tpolyhedra_domain.get_row_symb_value(row);
        lower_values[row]=
          simplify_const(
            solver.get(tpolyhedra_domain.strategy_value_exprs[row][0]));
        blocking_constraint.push_back(
          literal_exprt(!tpolyhedra_domain.strategy_cond_literals[row]));
        if(inv[row].is_neg_inf())
          improved_from_neginf=true;
      }
    }
    solver << conjunction(blocking_constraint);
  }
  solver.pop_context(); // improvement check

  if(!improved) // done
  {
#if 0
    debug() << "UNSAT" << eom;
#endif
    return improved;
  }

  // symbolic value system
  exprt pre_inv_expr=
    tpolyhedra_domain.to_symb_pre_constraints(inv, improve_rows);
  exprt post_inv_expr=
    tpolyhedra_domain.to_symb_post_constraints(improve_rows);

  assert(lower_values.size()>=1);
  std::map<tpolyhedra_domaint::rowt, symbol_exprt>::iterator
    it=symb_values.begin();
  exprt _lower=lower_values[it->first];
#if 1
  debug() << "update row " << it->first << ": "
          << from_expr(SSA.ns, "", lower_values[it->first]) << eom;
#endif
  inv[it->first]=lower_values[it->first];
  exprt _upper=
    tpolyhedra_domain.get_max_row_value(it->first);
  exprt sum=it->second;
  for(++it; it!=symb_values.end(); ++it)
  {
    sum=plus_exprt(sum, it->second);
    _upper=plus_exprt(_upper, tpolyhedra_domain.get_max_row_value(it->first));
    _lower=plus_exprt(_lower, lower_values[it->first]);

#if 1
    debug() << "update row " << it->first << ": "
            << from_expr(SSA.ns, "", lower_values[it->first]) << eom;
#endif
    inv[it->first]=lower_values[it->first];
  }

  // do not solve system if we have just reached a new loop
  //   (the system will be very large!)
  if(improved_from_neginf)
    return improved;

  solver.new_context(); // symbolic value system
  solver << pre_inv_expr;
  solver << post_inv_expr;

#if 1
  debug() << "symbolic value system: " << eom;
  debug() << "pre-inv: " << from_expr(SSA.ns, "", pre_inv_expr) << eom;
  debug() << "post-inv: " << from_expr(SSA.ns, "", post_inv_expr) << eom;
#endif

  extend_expr_types(sum);
  extend_expr_types(_upper);
  extend_expr_types(_lower);
  auto upper=tpolyhedra_domaint::row_valuet(simplify_const(_upper));
  auto lower=tpolyhedra_domaint::row_valuet(simplify_const(_lower));
  assert(sum.type()==upper.type());
  assert(sum.type()==lower.type());

  symbol_exprt sum_bound(
    SUM_BOUND_VAR+std::to_string(sum_bound_counter++),
    sum.type());
  solver << equal_exprt(sum_bound, sum);

#if 1
  debug() << from_expr(SSA.ns, "", equal_exprt(sum_bound, sum)) << eom;
#endif

  while(tpolyhedra_domain.less_than(lower, upper))
  {
    tpolyhedra_domaint::row_valuet middle=
      tpolyhedra_domain.between(lower, upper);
    if(!tpolyhedra_domain.less_than(lower, middle))
      middle=upper;

    // row_symb_value >= middle
    assert(sum_bound.type()==middle.type());
    exprt c=binary_relation_exprt(sum_bound, ID_ge, middle);

#if 1
    debug() << "upper: " << from_expr(SSA.ns, "", upper) << eom;
    debug() << "middle: " << from_expr(SSA.ns, "", middle) << eom;
    debug() << "lower: " << from_expr(SSA.ns, "", lower) << eom;
#endif

    solver.new_context(); // binary search iteration

#if 1
    debug() << "constraint: " << from_expr(SSA.ns, "", c) << eom;
#endif

    solver << c;

    if(solver()==decision_proceduret::D_SATISFIABLE)
    {
#if 0
      debug() << "SAT" << eom;
#endif

      lower=middle;

      for(const auto &sv : symb_values)
      {
#if 1
        debug() << "update row " << sv.first << " "
                << from_expr(SSA.ns, "", sv.second) << ": ";
#endif
        constant_exprt lower_row=
          simplify_const(solver.get(sv.second));
#if 1
        debug() << from_expr(SSA.ns, "", lower_row) << eom;
#endif
        inv[sv.first]=lower_row;
      }
    }
    else
    {
#if 0
      debug() << "UNSAT" << eom;
#endif

      if(!tpolyhedra_domain.less_than(middle, upper))
        middle=lower;

      upper=middle;
    }
    solver.pop_context(); // binary search iteration
  }

  solver.pop_context();  // symbolic value system

  return improved;
}
