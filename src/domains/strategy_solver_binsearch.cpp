#include <iostream>

#include "strategy_solver_binsearch.h"

bool strategy_solver_binsearcht::iterate(invariantt &_inv)
{
  template_domaint::templ_valuet &inv = 
    static_cast<template_domaint::templ_valuet &>(_inv);

  bool improved = false;

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
      debug() << "guards: " << 
       from_expr(ns, "", template_domain.templ.pre_guards[i]) << 
        " " << from_expr(ns, "", solver.get(template_domain.templ.pre_guards[i])) << eom;
      debug() << "guards: " << from_expr(ns, "", template_domain.templ.post_guards[i]) << " " 
	  << from_expr(ns, "", solver.get(template_domain.templ.post_guards[i])) << eom; 	     	     
    }    
          
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
      
    unsigned row=0;  
    for(;row<strategy_cond_literals.size(); row++)
    {
      if(solver.l_get(strategy_cond_literals[row]).is_true()) break;
    }

    debug() << "improving row: " << row << eom;

    template_domaint::row_valuet upper = 
      template_domain.get_max_row_value(row);
    template_domaint::row_valuet lower = 
      template_domain.get_min_row_value(row);
    //simplify_const(solver.get(strategy_value_exprs[row]));

    while(template_domain.less_than(lower,upper))   
    {
      template_domaint::row_valuet middle = 
	  template_domain.between(lower,upper);
      exprt c = template_domain.get_row_post_constraint(row,middle);

#if 0
      debug() << "upper: " << from_expr(ns,"",upper) << eom;
      debug() << "middle: " << from_expr(ns,"",middle) << eom;
      debug() << "lower: " << from_expr(ns,"",lower) << eom;
#endif
      
      replace_expr(renaming_map, c);

      literalt activation_literal = new_context();

#if 0
      debug() << "constraint: " << from_expr(ns, "", not_exprt(c)) << eom;
#endif

      solver << or_exprt(not_exprt(c),
			   literal_exprt(activation_literal)); // e > middle

      if(solver() == decision_proceduret::D_SATISFIABLE) 
      { 
#if 0
	debug() << "SAT" << eom;
#endif
	      
	if(!template_domain.less_than(lower,middle)) lower=upper;
	else lower = middle;
	    //simplify_const(solver.get(strategy_value_exprs[row]));
      }
      else 
      {
#if 0
	debug() << "UNSAT" << eom;
#endif

	upper = middle;
      }
      pop_context();
    }
   
#if 0
    debug() << "update value: " << from_expr(ns,"",lower) << eom;
#endif

    template_domain.set_row_value(row,lower,inv);
    improved = true;
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
  }

  pop_context();
  
  return improved;
}
