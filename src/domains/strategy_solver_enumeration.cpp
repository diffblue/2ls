#include <iostream>

#include "strategy_solver_enumeration.h"

void strategy_solver_enumerationt::solve(invariantt &inv, const strategyt &strategy)
{
  for(strategyt::const_iterator s_it = strategy.begin();
    s_it != strategy.end(); s_it++)
  {
    std::cout << "get model for " << *s_it << std::endl;
    template_domaint::row_valuet v = to_constant_expr(solver.get(strategy_value_exprs[*s_it]));
    template_domain.set_row_value(*s_it,v,inv);
  }

  //delete context
}
