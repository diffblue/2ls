#include <iostream>

#include "strategy_solver_binsearch.h"

void strategy_solver_binsearcht::solve(invariantt &inv, const strategyt &strategy)
{
  for(strategyt::const_iterator s_it = strategy.begin();
    s_it != strategy.end(); s_it++)
  {

#if 1
    debug() << "processing strategy: " << *s_it << eom;
#endif

    template_domaint::row_valuet upper = template_domain.get_max_row_value(*s_it);
    template_domaint::row_valuet lower = simplify_const(solver.get(strategy_value_exprs[*s_it]));
    template_domaint::row_valuet middle = upper;

 
    while (template_domain.less_than(lower,middle))   
    {
      middle = template_domain.between(lower,upper);
      exprt c = template_domain.get_row_post_constraint(*s_it,middle);

#if 0
      debug() << "upper: " << from_expr(ns,"",upper) << eom;
      debug() << "middle: " << from_expr(ns,"",middle) << eom;
      debug() << "lower: " << from_expr(ns,"",lower) << eom;
#endif
  
      replace_expr(renaming_map, c);

      literalt activation_literal = new_context();
      //      debug() << "constraint: " << from_expr(ns, "", not_exprt(c)) << eom;
      solver << or_exprt(not_exprt(c),
			 literal_exprt(activation_literal)); // e > middle

      if(solver() == decision_proceduret::D_SATISFIABLE) 
      { 
#if 0
	debug() << "SAT" << eom;
#endif

        lower = middle;
        //simplify_const(solver.get(strategy_value_exprs[*s_it]));
      }
      else 
      {
#if 0
	debug() << "UNSAT" << eom;
#endif

        upper = middle;
      }
      pop_context();
    }
   
#if 1
    debug() << "update value: " << from_expr(ns,"",lower) << eom;
#endif

    template_domain.set_row_value(*s_it,lower,inv);
  }
  pop_context();
}
