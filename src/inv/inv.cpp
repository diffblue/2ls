#include "inv.h"
#include "strategy_solver_base.h"

void invt::solve(class invariantt &inv)
{
  strategy_solver_baset::strategyt strategy;
  while(strategy_solver.improve(inv,strategy))
  {
    strategy_solver.solve(inv,strategy);
  }
}
