#include <iostream>
#include <set>
#include <cmath>

#include <solvers/flattening/bv_pointers.h>
#include <util/i2string.h>

#include "strategy_solver_base.h"

bool strategy_solver_baset::improve(const invariantt &inv, strategyt &strategy)
{
  strategy.clear();

  literalt activation_literal = new_context();

  exprt inv_expr = template_domain.to_pre_constraints(inv);
  std::cout << "inv: " << from_expr(ns,"",inv_expr) << std::endl;
  solver << or_exprt(inv_expr,
    literal_exprt(activation_literal)); 

  exprt::operandst strategy_cond_exprs;
  template_domain.make_not_post_constraints(inv, 
    strategy_cond_exprs, strategy_value_exprs); 
  
  rename(strategy_cond_exprs);
  rename(strategy_value_exprs);
  
  strategy_cond_literals.resize(strategy_cond_exprs.size());
  
  for(unsigned i = 0; i<strategy_cond_exprs.size(); i++)
  {  
    std::cout << "cond_expr: " << from_expr(ns,"",strategy_cond_exprs[i]) << std::endl;

    bvt bv(solver.convert_bv(strategy_cond_exprs[i]));
    solver.set_frozen(bv);
    strategy_cond_literals[i] = bv[0];
    strategy_cond_exprs[i] = literal_exprt(strategy_cond_literals[i]);
  }
  
  solver << or_exprt(disjunction(strategy_cond_exprs),
     literal_exprt(activation_literal)); 

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
	  std::cout << "adding to strategy: " << row << std::endl;
          strategy.push_back(row);
          //add blocking constraint
          //solver << or_exprt(literal_exprt(!strategy_cond_literals[row]),
	  //	      literal_exprt(activation_literal));
      	}
      }
      assert(strategy.size()>0);
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

literalt strategy_solver_baset::new_context() 
{
  literalt activation_literal = solver.convert(
      symbol_exprt("goto_symex::\\act$"+
      i2string(activation_literal_counter++), bool_typet()));

  activation_literals.push_back(activation_literal);
  solver.set_assumptions(activation_literals);
  return !activation_literals.back();
}

void strategy_solver_baset::pop_context() 
{
  assert(!activation_literals.empty());
  literalt activation_literal = activation_literals.back();
  activation_literals.pop_back();
  solver.set_to_true(literal_exprt(activation_literal));
  solver.set_assumptions(activation_literals);
}
