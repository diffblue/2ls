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
#ifdef DEBUG_OUTPUT
  debug() << "pre-inv: " << from_expr(ns,"",pre_expr) << eom;
#endif
  solver << pre_expr;

  // Exit value constraints
  exprt::operandst strategy_cond_exprs;
  heap_domain.make_not_post_constraints(inv, strategy_cond_exprs, strategy_value_exprs);

  strategy_cond_literals.resize(strategy_cond_exprs.size());

#ifdef DEBUG_OUTPUT
  debug() << "post-inv: ";
#endif
  for (unsigned i = 0; i < strategy_cond_exprs.size(); ++i)
  {
#ifdef DEBUG_OUTPUT
    debug() << (i>0 ? " || " : "") << from_expr(ns,"",strategy_cond_exprs[i]) ;
#endif
    strategy_cond_literals[i] = solver.convert(strategy_cond_exprs[i]);
    strategy_cond_exprs[i] = literal_exprt(strategy_cond_literals[i]);
  }
#ifdef DEBUG_OUTPUT
  debug() << eom;
#endif
  solver << disjunction(strategy_cond_exprs);

  #ifdef DEBUG_OUTPUT
  debug() << "solve(): ";
#endif

  if (solver() == decision_proceduret::D_SATISFIABLE)  // improvement check
  {
#ifdef DEBUG_OUTPUT
    debug() << "SAT" << eom;
#endif

#ifdef DEBUG_OUTPUT
    for(unsigned i=0; i<solver.activation_literals.size(); i++)
    {
      debug() << "literal: " << solver.activation_literals[i] << " " <<
        solver.l_get(solver.activation_literals[i]) << eom;
    }
    for(unsigned i=0; i<solver.formula.size(); i++)
    {
      debug() << "literal: " << solver.formula[i] << " " <<
        solver.l_get(solver.formula[i]) << eom;
    }
    for(unsigned i=0; i<heap_domain.templ.size(); i++)
    {
      exprt c = heap_domain.get_row_pre_constraint(i,inv[i]);
      debug() << "cond: " << from_expr(ns, "", c) << " " <<
          from_expr(ns, "", solver.get(c)) << eom;
      debug() << "guards: " << from_expr(ns, "", heap_domain.templ[i].pre_guard) <<
          " " << from_expr(ns, "", solver.get(heap_domain.templ[i].pre_guard)) << eom;
      debug() << "guards: " << from_expr(ns, "", heap_domain.templ[i].post_guard) << " "
          << from_expr(ns, "", solver.get(heap_domain.templ[i].post_guard)) << eom;
    }
#endif

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
  else
  {
#ifdef DEBUG_OUTPUT
    debug() << "UNSAT" << eom;
#endif

#ifdef DEBUG_OUTPUT
    for(unsigned i=0; i<solver.formula.size(); i++)
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
