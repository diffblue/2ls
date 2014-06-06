#include "strategy_solver_base.h"

bool strategy_solver_baset::improve(const invariantt &inv, strategyt &strategy)
{
  solver << program.convert();
  solver << template_domain.convert(inv);
  solver << template_domain.convert(template_domain.complement(inv),loopvars);
  modelt model = solver.decide();
  if(satisfiable) 
  {
    strategy[model.row] = model.multiplexer_state;
    return true;
  }
  return false;
}
