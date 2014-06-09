#include <set>

#include "strategy_solver_base.h"

bool strategy_solver_baset::improve(const invariantt &inv, strategyt &strategy)
{
  solver << template_domain.to_constraints(inv);
  solver << template_domain.to_not_constraints(inv);
  modelt model = solver.decide();
  if(satisfiable) 
  {
    strategy[model.row] = model.multiplexer_state;
    return true;
  }
  return false;
}
