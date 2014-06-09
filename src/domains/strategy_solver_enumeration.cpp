#include "strategy_solver_enumeration.h"

void strategy_solver_enumerationt::solve(invariantt &inv, const strategyt &strategy)
{
  for(strategyt::const_iterator s_it = strategy.begin();
    s_it != strategy.end(); s_it++)
  {
    //get model 
  
    //new context
 
    exprt c = template_domain.get_row_constraint(*s_it,inv);

    solver << not_exprt(c);
    if(solver() == decision_proceduret::D_SATISFIABLE) 
    {
      //inv[s_it->first] = model;  
    }
   //delete context
  }
}
