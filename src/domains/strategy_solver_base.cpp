#include <set>
#include <cmath>

#include <util/i2string.h>

#include "strategy_solver_base.h"

bool strategy_solver_baset::improve(const invariantt &inv, strategyt &strategy)
{
  strategy.clear();

  //new context
  solver << template_domain.to_constraints(inv); //TODO: add assumption literal

  exprt::operandst strategy_cond_exprs;
  template_domain.make_not_constraints(inv, strategy_cond_exprs, strategy_value_exprs); 
  
  rename(strategy_cond_exprs);
  rename(strategy_value_exprs);
  
  strategy_cond_literals.resize(strategy_cond_exprs.size());
  
  for(unsigned i = 0; i<strategy_cond_exprs.size(); i++)
  {
    strategy_cond_literals[i] = solver.convert(strategy_cond_exprs[i]);
    strategy_cond_exprs[i] = literal_exprt(strategy_cond_literals[i]);
  }
  solver << disjunction(strategy_cond_exprs); //TODO: add assumption literal

  bool first = true;
  while(true)
  {
    if(solver() == decision_proceduret::D_SATISFIABLE) 
    { 
      for(unsigned row=0;row<strategy_cond_literals.size(); row++)
      {
        if(solver.l_get(strategy_cond_literals[row]).is_true()) 
	      {
          strategy.push_back(row);
          //add blocking constraint
          solver << literal_exprt(!strategy_cond_literals[row]); //TODO: add assumption literal
      	}
      }
    }
    else if(first) return false;
    first = false;
  }
}

