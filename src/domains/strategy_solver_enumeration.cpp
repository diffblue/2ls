#include <iostream>

#include <util/simplify_expr.h>
#include "strategy_solver_enumeration.h"

void strategy_solver_enumerationt::solve(invariantt &inv, const strategyt &strategy)
{
  for(strategyt::const_iterator s_it = strategy.begin();
    s_it != strategy.end(); s_it++)
  {
    //    std::cout << "get model for row " << *s_it << std::endl;
    exprt value = solver.get(strategy_value_exprs[*s_it]);
    //    std::cout << "raw value: " << from_expr(ns,"",value) << std::endl;
    template_domaint::row_valuet v = simplify_const(value);
    std::cout << "simplified value: " << from_expr(ns,"",v) << std::endl;
    template_domain.set_row_value(*s_it,v,inv);
  }
  
  //delete context
}
