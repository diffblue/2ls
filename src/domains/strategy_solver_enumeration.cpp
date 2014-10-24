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

  solver.new_context();

  exprt preinv_expr = tpolyhedra_domain.to_pre_constraints(inv);
  debug() << "pre-inv: " << from_expr(ns,"",preinv_expr) << eom;

  solver << preinv_expr;

  exprt::operandst strategy_cond_exprs;
  tpolyhedra_domain.make_not_post_constraints(inv, 
    strategy_cond_exprs, strategy_value_exprs); 
  
  strategy_cond_literals.resize(strategy_cond_exprs.size());
  
  exprt postinv_expr = disjunction(strategy_cond_exprs);

  debug() << "post-inv: ";
  for(unsigned i = 0; i<strategy_cond_exprs.size(); i++)
  {  
    debug() << (i>0 ? " || " : "") << from_expr(ns,"",strategy_cond_exprs[i]) ;

    strategy_cond_literals[i] = solver.solver.convert(strategy_cond_exprs[i]);
    //solver.set_frozen(strategy_cond_literals[i]);
    strategy_cond_exprs[i] = literal_exprt(strategy_cond_literals[i]);
  }
  debug() << eom;

  solver << disjunction(strategy_cond_exprs);

  debug() << "solve(): ";

  if(solver() == decision_proceduret::D_SATISFIABLE) 
  { 
    debug() << "SAT" << eom;
      
    #if 0
    for(unsigned i=0; i<solver.formula.size(); i++) 
    {
      debug() << "literal: " << solver.formula[i] << " " << 
        solver.solver.l_get(solver.formula[i]) << eom;
    }
    for(unsigned i=0; i<tpolyhedra_domain.template_size(); i++) 
    {
      exprt c = tpolyhedra_domain.get_row_constraint(i,inv[i]);
      debug() << "cond: " << from_expr(ns, "", c) << " " << 
          from_expr(ns, "", solver.solver.get(c)) << eom;
      debug() << "guards: " << from_expr(ns, "", tpolyhedra_domain.templ.pre_guards[i]) << 
          " " << from_expr(ns, "", solver.get(tpolyhedra_domain.templ.pre_guards[i])) << eom;
      debug() << "guards: " << from_expr(ns, "", tpolyhedra_domain.templ.post_guards[i]) << " " 
          << from_expr(ns, "", solver.solver.get(tpolyhedra_domain.templ.post_guards[i])) << eom; 	     	     
    }    
          
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
      if(solver.solver.l_get(strategy_cond_literals[row]).is_true()) 
      {
        debug() << "updating row: " << row << eom;

        exprt value = solver.solver.get(strategy_value_exprs[row]);
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

#ifdef DEBUG_OUTPUT
    for(unsigned i=0; i<solver.formula.size(); i++) 
    {
      if(solver.solver.is_in_conflict(solver.formula[i]))
        debug() << "is_in_conflict: " << solver.formula[i] << eom;
      else
        debug() << "not_in_conflict: " << solver.formula[i] << eom;
     }
#endif    
  }
  solver.pop_context();

  return improved;
}
