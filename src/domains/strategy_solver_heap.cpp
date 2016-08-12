/**
 *  Viktor Malik, 12.8.2016 (c).
 */

#include "strategy_solver_heap.h"

bool strategy_solver_heapt::iterate(invariantt &_inv)
{
  heap_domaint::heap_valuet &inv = static_cast<heap_domaint::heap_valuet &>(_inv);

  auto n_it = todo_nulls.begin();
  if (n_it != todo_nulls.end())  // check NULL pointers
  {
    solver.new_context();

    exprt pre_expr = heap_domain.get_pre_null_constraint(*n_it);

    solver << pre_expr;

    exprt post_expr = heap_domain.get_post_not_null_constraint(*n_it);
    literalt cond_literal = solver.convert(post_expr);

    solver << literal_exprt(cond_literal);

    if (solver() == decision_proceduret::D_SATISFIABLE)
    {
    }
    else  // equality holds
    {
      heap_domain.set_null(*n_it, inv);

      solver << pre_expr;  // make permanent
    }

    solver.pop_context();

    todo_nulls.erase(n_it);
    return true;
  }
  else
  {
    return false;
  }
}
