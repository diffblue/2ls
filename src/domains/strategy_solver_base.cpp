#include <set>

#include "strategy_solver_base.h"

bool strategy_solver_baset::improve(const invariantt &inv, strategyt &strategy)
{
  solver << template_domain.to_constraints(inv);
  solver << template_domain.to_not_constraints(inv);
  bool first = true;
  while(true)
  {
    if(solver() == decision_proceduret::D_SATISFIABLE) 
    { 
      //modelt model = solver.get_model();
      //template_domaint::rowt row = get_violating_template_row(model);
      //strategy.push_back(row);
      //solver << get_blocking_constraint(row);
    }
    else if(first) return false;
    first = false;
  }
}
