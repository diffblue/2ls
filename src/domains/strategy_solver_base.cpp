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
  debug() << "pre-inv: " << from_expr(ns,"",inv_expr) << eom;

#ifndef DEBUG_FORMULA
  solver << or_exprt(inv_expr, literal_exprt(activation_literal));
#else
  debug() << "literal " << activation_literal << eom;
  literalt l = solver.convert(or_exprt(inv_expr, literal_exprt(activation_literal)));
  if(!l.is_constant()) 
  {
    debug() << "literal " << l << ": " << from_expr(ns,"",or_exprt(inv_expr, literal_exprt(activation_literal))) <<eom;
    formula.push_back(l);
  }
#endif

  exprt::operandst strategy_cond_exprs;
  template_domain.make_not_post_constraints(inv, 
    strategy_cond_exprs, strategy_value_exprs); 
  
  rename(strategy_cond_exprs);
  rename(strategy_value_exprs);
  
  strategy_cond_literals.resize(strategy_cond_exprs.size());
  
  debug() << "post-inv: ";
  for(unsigned i = 0; i<strategy_cond_exprs.size(); i++)
  {  
    debug() << (i>0 ? " || " : "") << from_expr(ns,"",strategy_cond_exprs[i]) ;

    strategy_cond_literals[i] = solver.convert(strategy_cond_exprs[i]);
    //solver.set_frozen(strategy_cond_literals[i]);
    strategy_cond_exprs[i] = literal_exprt(strategy_cond_literals[i]);
  }
  debug() << eom;


#ifndef DEBUG_FORMULA
  solver << or_exprt(disjunction(strategy_cond_exprs),
		     literal_exprt(activation_literal));
#else

  exprt expr_act=
    or_exprt(disjunction(strategy_cond_exprs),
	       literal_exprt(activation_literal));

  l = solver.convert(expr_act);
  if(!l.is_constant()) 
  {
    debug() << "literal " << l << ": " << 
      from_expr(ns,"", expr_act) <<eom;
    formula.push_back(l);
  }
#endif

  bool first = true;
  while(true)
  {
    debug() << "solver(): ";

#ifdef DEBUG_FORMULA
    bvt whole_formula = formula;
    whole_formula.insert(whole_formula.end(),activation_literals.begin(),activation_literals.end());
    solver.set_assumptions(whole_formula);
#endif

    if(solver() == decision_proceduret::D_SATISFIABLE) 
    { 
      debug() << "SAT" << eom;
      
      #ifdef DEBUG_FORMULA
      for(unsigned i=0; i<whole_formula.size(); i++) 
      {
 	debug() << "literal: " << whole_formula[i] << " " << 
          solver.l_get(whole_formula[i]) << eom;
      }
          
      for(unsigned i=0; i<template_domain.templ.size(); i++) 
      {
        exprt c = template_domain.get_row_constraint(i,inv[i]);
 	debug() << "cond: " << from_expr(ns, "", c) << " " << 
          from_expr(ns, "", solver.get(c)) << eom;
 	debug() << "guards: " << from_expr(ns, "", template_domain.templ.pre_guards[i]) << 
          " " << from_expr(ns, "", solver.get(template_domain.templ.pre_guards[i])) << eom;
 	debug() << "guards: " << from_expr(ns, "", template_domain.templ.post_guards[i]) << " " 
          << from_expr(ns, "", solver.get(template_domain.templ.post_guards[i])) << eom; 	     	     }    
          
      for(replace_mapt::const_iterator
          it=renaming_map.begin();
          it!=renaming_map.end();    
          ++it)
          
      {
        debug() << "replace_map (1st): " << from_expr(ns, "", it->first) << " " << 
          from_expr(ns, "", solver.get(it->first)) << eom;
        debug() << "replace_map (2nd): " << from_expr(ns, "", it->second) << " " << 
          from_expr(ns, "", solver.get(it->second)) << eom;
      }
                  
      #endif
      
      
      for(unsigned row=0;row<strategy_cond_literals.size(); row++)
      {
        if(solver.l_get(strategy_cond_literals[row]).is_true()) 
      	{
      	  debug() << "adding to strategy: " << row << eom;
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
      debug() << "UNSAT" << eom;

#ifdef DEBUG_FORMULA
      for(unsigned i=0; i<whole_formula.size(); i++) 
      {
        if(solver.is_in_conflict(whole_formula[i]))
   	      debug() << "is_in_conflict: " << whole_formula[i] << eom;
   	    else
  	      debug() << "not_in_conflict: " << whole_formula[i] << eom;
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

#if 0
    debug() << "new context: " << activation_literal<< eom;
#endif

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
  solver.set_to_false(literal_exprt(activation_literal));
#else
  formula.push_back(!activation_literal);
#endif

#if 0
    debug() << "pop context: " << activation_literal<< eom;
#endif

  solver.set_assumptions(activation_literals);
}
