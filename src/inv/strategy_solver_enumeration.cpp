#include "strategy_solver_enumeration.h"

bool strategy_solver_baset::solve(invariantt &inv, const strategyt &strategy)
{
  template_domaint::valuet lower = template_domain.get_lower();
  template_domaint::valuet upper = template_domain.get_upper();
  
  solver << program.convert();
  solver << template_domain.convert(inv);
  for(s_it,strategy)
  {
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
