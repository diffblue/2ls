#include <set>
#include <cmath>

#include <util/i2string.h>

#include "strategy_solver_base.h"

bool strategy_solver_baset::improve(const invariantt &inv, strategyt &strategy)
{
  strategy.clear();
  solver << template_domain.to_constraints(inv); //TODO: add assumption literal
  exprt c = template_domain.to_not_constraints(inv); //TODO: add assumption literal
  preprocess_template_rows(c);
  solver << c; //TODO: add assumption literal
  bool first = true;
  while(true)
  {
    if(solver() == decision_proceduret::D_SATISFIABLE) 
    { 
      for(unsigned row=0;row<strategy_literals.size(); row++)
      {
        if(solver.l_get(strategy_literals[row]).is_true()) 
	{
          strategy.push_back(row);
          //add blocking constraint
          solver << literal_exprt(!strategy_literals[row]); //TODO: add assumption literal
	}
      }
    }
    else if(first) return false;
    first = false;
  }
}

void strategy_solver_baset::preprocess_template_rows(exprt &expr)
{
  assert(expr.id()==ID_or);
  assert(expr.operands().size()==template_domain.template_size());
  strategy_literals.reserve(expr.operands().size());
  for(unsigned i = 0; i<expr.operands().size(); i++)
  {
    strategy_literals[i] = solver.convert(expr.operands()[i]);
    expr.operands()[i] = literal_exprt(strategy_literals[i]);
  }
}
