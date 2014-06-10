#include <iostream>
#include <set>
#include <cmath>

#include <solvers/flattening/bv_pointers.h>
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
    std::cout << "cond_expr: " << strategy_cond_exprs[i] << std::endl;

    bvt bv(solver.convert_bv(strategy_cond_exprs[i]));
  
    solver.set_frozen(bv);
  
    strategy_cond_literals[i] = bv[0];
        
    strategy_cond_exprs[i] = literal_exprt(strategy_cond_literals[i]);
    
    std::cout << "literal " << (strategy_cond_literals[i].is_false() ? "0" : strategy_cond_literals[i].is_true() ? "1" : "X") << std::endl;

  }
  solver << disjunction(strategy_cond_exprs); //TODO: add assumption literal

  bool first = true;
  while(true)
  {
    std::cout << "solver(): ";
    if(solver() == decision_proceduret::D_SATISFIABLE) 
    { 
      std::cout << "SAT" << std::endl;
      for(unsigned row=0;row<strategy_cond_literals.size(); row++)
      {
        if(solver.l_get(strategy_cond_literals[row]).is_true()) 
	{
          strategy.push_back(row);
          //add blocking constraint
          solver << literal_exprt(!strategy_cond_literals[row]); //TODO: add assumption literal
      	}
      }
      return true; //skip outer loop
    }
    else 
    {
      std::cout << "UNSAT" << std::endl;
      if(first) return false;
      return true;
    }
    first = false;
  }
}

