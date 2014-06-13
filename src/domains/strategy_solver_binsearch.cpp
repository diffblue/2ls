#include <iostream>

#include "strategy_solver_binsearch.h"

void strategy_solver_binsearcht::solve(invariantt &inv, const strategyt &strategy)
{
  for(strategyt::const_iterator s_it = strategy.begin();
    s_it != strategy.end(); s_it++)
  {
    std::cout << "processing strategy: " << *s_it << std::endl;
    template_domaint::row_valuet upper = template_domain.get_max_row_value(*s_it);
    template_domaint::row_valuet lower = to_constant_expr(solver.get(strategy_value_exprs[*s_it]));

 
    while (template_domain.leq(lower,upper))   
    {
      template_domaint::row_valuet middle = template_domain.between(lower,upper);
      exprt c = template_domain.get_row_constraint(*s_it,middle);

      std::cout << "upper: " << from_expr(ns,"",upper) << std::endl;
      std::cout << "middle: " << from_expr(ns,"",middle) << std::endl;
      std::cout << "lower: " << from_expr(ns,"",lower) << std::endl;
  
      replace_expr(renaming_map, c);

      //new context
      solver << not_exprt(c); // e > middle, TODO: add assumption literal

      if(solver() == decision_proceduret::D_SATISFIABLE) lower = middle; //model;
      else upper = middle;

      //delete context
    }
   
    std::cout << "update value: " << from_expr(ns,"",lower) << std::endl;
    template_domain.set_row_value(*s_it,lower,inv);
  }
  //delete context
}
