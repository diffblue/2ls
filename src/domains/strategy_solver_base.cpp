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
  std::cout << "pre-inv: " << from_expr(ns,"",inv_expr) << std::endl;

#ifndef DEBUG_FORMULA
  solver << or_exprt(inv_expr, literal_exprt(activation_literal));
#else
  std::cout << "literal " << activation_literal << std::endl;
  literalt l = solver.convert(or_exprt(inv_expr, literal_exprt(activation_literal)));
  if(!l.is_constant()) 
  {
    std::cout << "literal " << l << ": " << from_expr(ns,"",inv_expr) << std::endl;
    formula.push_back(l);
  }
#endif

  exprt::operandst strategy_cond_exprs;
  template_domain.make_not_post_constraints(inv, 
    strategy_cond_exprs, strategy_value_exprs); 
  
  rename(strategy_cond_exprs);
  rename(strategy_value_exprs);
  
  strategy_cond_literals.resize(strategy_cond_exprs.size());
  
  std::cout << "post-inv: ";
  for(unsigned i = 0; i<strategy_cond_exprs.size(); i++)
  {  
    std::cout << (i>0 ? " || " : "") << from_expr(ns,"",strategy_cond_exprs[i]) ;

    strategy_cond_literals[i] = solver.convert(strategy_cond_exprs[i]);
    //solver.set_frozen(strategy_cond_literals[i]);
    strategy_cond_exprs[i] = literal_exprt(strategy_cond_literals[i]);
  }
  std::cout << std::endl;


#ifndef DEBUG_FORMULA
  solver << or_exprt(disjunction(strategy_cond_exprs),
		     literal_exprt(activation_literal));
#else
  l = solver.convert(
      or_exprt(disjunction(strategy_cond_exprs),
	       literal_exprt(activation_literal)));
  if(!l.is_constant()) 
  {
    std::cout << "literal " << l << ": " << 
      from_expr(ns,"",disjunction(strategy_cond_exprs)) << std::endl;
    formula.push_back(l);
  }
#endif

  bool first = true;
  while(true)
  {
    std::cout << "solver(): ";

#ifdef DEBUG_FORMULA
    bvt whole_formula = formula;
    whole_formula.insert(whole_formula.end(),activation_literals.begin(),activation_literals.end());
    solver.set_assumptions(whole_formula);
#endif

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

#ifdef DEBUG_FORMULA
      for(unsigned i=0; i<formula.size(); i++) 
      {
        if(solver.is_in_conflict(formula[i]))
   	  std::cout << "is_in_conflict: " << formula[i] << std::endl;
      }
#endif

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
#ifndef DEBUG_FORMULA
  solver.set_to_true(literal_exprt(activation_literal));
#else
  formula.push_back(activation_literal);
#endif
  solver.set_assumptions(activation_literals);
}
