#include <iostream>

#include "strategy_solver_binsearch.h"

void strategy_solver_binsearcht::solve(invariantt &inv, const strategyt &strategy)
{
  for(strategyt::const_iterator s_it = strategy.begin();
    s_it != strategy.end(); s_it++)
  {

#if 1
    std::cout << "processing strategy: " << *s_it << std::endl;
#endif

    template_domaint::row_valuet upper = template_domain.get_max_row_value(*s_it);
    template_domaint::row_valuet lower = simplify_const(solver.get(strategy_value_exprs[*s_it]));

 
    while (template_domain.less_than(lower,upper))   
    {
      template_domaint::row_valuet middle = template_domain.between(lower,upper);
      exprt c = template_domain.get_row_post_constraint(*s_it,middle);

#if 1
      std::cout << "upper: " << from_expr(ns,"",upper) << std::endl;
      std::cout << "middle: " << from_expr(ns,"",middle) << std::endl;
      std::cout << "lower: " << from_expr(ns,"",lower) << std::endl;
#endif
  
      replace_expr(renaming_map, c);

      literalt activation_literal = new_context();
      solver << or_exprt(not_exprt(c),
			 literal_exprt(activation_literal)); // e > middle

      if(solver() == decision_proceduret::D_SATISFIABLE) lower = middle; //model;
      else upper = middle;

      pop_context();
    }
   
#if 1
    std::cout << "update value: " << from_expr(ns,"",lower) << std::endl;
#endif

    template_domain.set_row_value(*s_it,lower,inv);
  }
  pop_context();
}
