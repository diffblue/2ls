#include <iostream>

#include <util/simplify_expr.h>
#include <util/find_symbols.h>

#include "strategy_solver_enumeration.h"
#include "util.h"

bool strategy_solver_enumerationt::iterate(invariantt &_inv)
{
  tpolyhedra_domaint::templ_valuet &inv = 
    static_cast<tpolyhedra_domaint::templ_valuet &>(_inv);

  bool improved = false;

  literalt activation_literal = new_context();

  exprt preinv_expr = tpolyhedra_domain.to_pre_constraints(inv);
  debug() << "pre-inv: " << from_expr(ns,"",preinv_expr) << eom;
  preinv_expr = or_exprt(preinv_expr, literal_exprt(activation_literal));

#ifndef DEBUG_FORMULA
  solver << preinv_expr;
#else
  debug() << "literal " << activation_literal << eom;
  debug_add_to_formula(preinv_expr);
#endif

  exprt::operandst strategy_cond_exprs;
  tpolyhedra_domain.make_not_post_constraints(inv, 
    strategy_cond_exprs, strategy_value_exprs); 
  
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

  exprt postinv_expr = or_exprt(disjunction(strategy_cond_exprs),
				literal_exprt(activation_literal));
#ifndef DEBUG_FORMULA
  solver << postinv_expr;
#else
  debug_add_to_formula(postinv_expr);
#endif

  debug() << "solve(): ";

#ifdef DEBUG_FORMULA
  bvt whole_formula = formula;
  whole_formula.insert(whole_formula.end(),activation_literals.begin(),activation_literals.end());
  solver.set_assumptions(whole_formula);
#endif

  if(solve() == decision_proceduret::D_SATISFIABLE) 
  { 
    debug() << "SAT" << eom;
      
    #ifdef DEBUG_FORMULA
    for(unsigned i=0; i<whole_formula.size(); i++) 
    {
      debug() << "literal: " << whole_formula[i] << " " << 
        solver.l_get(whole_formula[i]) << eom;
    }
    #endif
          
    #if 0
    for(unsigned i=0; i<tpolyhedra_domain.template_size(); i++) 
    {
      exprt c = tpolyhedra_domain.get_row_constraint(i,inv[i]);
      debug() << "cond: " << from_expr(ns, "", c) << " " << 
          from_expr(ns, "", solver.get(c)) << eom;
      debug() << "guards: " << from_expr(ns, "", tpolyhedra_domain.templ.pre_guards[i]) << 
          " " << from_expr(ns, "", solver.get(tpolyhedra_domain.templ.pre_guards[i])) << eom;
      debug() << "guards: " << from_expr(ns, "", tpolyhedra_domain.templ.post_guards[i]) << " " 
      << from_expr(ns, "", solver.get(tpolyhedra_domain.templ.post_guards[i])) << eom; 	    	    
    }    
    #endif
          
    #if 1
    {
      std::set<symbol_exprt> vars;
      find_symbols(preinv_expr,vars); 

      for(std::set<symbol_exprt>::const_iterator
	    it=vars.begin();
          it!=vars.end();    
          ++it)
      {
	debug() << "var: " << from_expr(ns, "", *it) << " = " << 
          from_expr(ns, "", solver.get(*it)) << eom;
      }
    }
    for(unsigned i=0; i<tpolyhedra_domain.template_size(); i++) 
    {
      std::set<symbol_exprt> vars;
      find_symbols(strategy_value_exprs[i],vars); 

      for(std::set<symbol_exprt>::const_iterator
	    it=vars.begin();
          it!=vars.end();    
          ++it)
      {
	debug() << "var: " << from_expr(ns, "", *it) << " = " << 
          from_expr(ns, "", solver.get(*it)) << eom;
      }
    }
    #endif
      
      
    for(unsigned row=0;row<strategy_cond_literals.size(); row++)
    {
      if(solver.l_get(strategy_cond_literals[row]).is_true()) 
      {
        debug() << "updating row: " << row << eom;

        exprt value = solver.get(strategy_value_exprs[row]);
        tpolyhedra_domaint::row_valuet v = simplify_const(value);

        debug() << "raw value; " << from_expr(ns, "", value) << 
          ", simplified value: " << from_expr(ns,"",v) << eom;

        tpolyhedra_domain.set_row_value(row,v,inv);
      }
    }
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
