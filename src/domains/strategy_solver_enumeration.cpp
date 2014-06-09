#include "strategy_solver_enumeration.h"

bool strategy_solver_baset::solve(invariantt &inv, const strategyt &strategy)
{
  for(s_it,strategy)
  {
    //get model 
  
    //new context
    solver << s_it->second;
 
    exprt c = template_domain.get_row_constraint(s_it->first);

    solver << not_exprt(c);
    modelt model = solver.decide();
    if(satisfiable) 
    {
      inv[s_it->first] = model;  
    }
   //delete context
  }
  return false;
}
