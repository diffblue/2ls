#include "strategy_solver_binsearch.h"

void strategy_solver_binsearcht::solve(invariantt &inv, const strategyt &strategy)
{
  for(strategyt::const_iterator s_it = strategy.begin();
    s_it != strategy.end(); s_it++)
  {
    template_domaint::row_valuet v = to_constant_expr(solver.get(strategy_value_exprs[*s_it]));

    template_domaint::row_valuet upper = template_domain.get_max_row_value(*s_it);
    template_domaint::row_valuet lower = to_constant_expr(solver.get(strategy_value_exprs[*s_it]));
 
    while (template_domain.leq(lower,upper))   
    {
      template_domaint::row_valuet middle = template_domain.between(lower,upper);
      exprt c = template_domain.get_row_constraint(*s_it,middle);

      //new context
      solver << not_exprt(c); // e > middle, TODO: add assumption literal

      if(solver() == decision_proceduret::D_SATISFIABLE) lower = middle; //model;
      else upper = middle;

      //delete context
    }
   
    template_domain.set_row_value(*s_it,lower,inv);
  }
  //delete context
}
