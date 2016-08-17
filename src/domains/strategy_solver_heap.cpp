/**
 *  Viktor Malik, 12.8.2016 (c).
 */

#include "strategy_solver_heap.h"

bool strategy_solver_heapt::iterate(invariantt &_inv)
{
  heap_domaint::heap_valuet &inv = static_cast<heap_domaint::heap_valuet &>(_inv);

  bool improved = false;

  solver.new_context();

  // Entry value constraints
  exprt pre_expr = heap_domain.to_pre_constraints(inv);
  solver << pre_expr;

  // Exit value constraints
  exprt::operandst strategy_cond_exprs;
  heap_domain.make_not_post_constraints(inv, strategy_cond_exprs, strategy_value_exprs);

  strategy_cond_literals.resize(strategy_cond_exprs.size());

  for (unsigned i = 0; i < strategy_cond_exprs.size(); ++i)
  {
    strategy_cond_literals[i] = solver.convert(strategy_cond_exprs[i]);
    strategy_cond_exprs[i] = literal_exprt(strategy_cond_literals[i]);
  }
  solver << disjunction(strategy_cond_exprs);

  if (solver() == decision_proceduret::D_SATISFIABLE)  // improvement check
  {
    for (unsigned row = 0; row < strategy_cond_literals.size(); ++row)
    {
      if (solver.l_get(strategy_cond_literals[row]).is_true())
      {
        debug() << "updating row: " << row << eom;

        exprt value = solver.get(strategy_value_exprs[row]);
        // Value from solver must be converted into expression
        exprt dest = heap_domain.value_to_ptr_exprt(value);

        debug() << "destination: " << from_expr(ns, "", dest) << eom;

        if (heap_domain.add_row_dest(row, inv, dest))
          improved = true;
      }
    }
  }
  solver.pop_context();

  return improved;

}
