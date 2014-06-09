#include "strategy_solver_binary_search.h"

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
 
    while (lower <= upper)   
    {
      template_domaint::valuet middle = template_domain.between(lower,upper);
      exprt c = template_domain.make_row_constraint(s_it->first,middle);

      solver << not_exprt(c); // e > middle
      modelt model = solver.decide();
      if(satisfiable) 
      {
        lower = middle; //model;
      }
      else
      {
        upper = middle;
      }
    }
   
    inv[s_it->first] = lower;  

    //delete context
  }
  return false;
}
