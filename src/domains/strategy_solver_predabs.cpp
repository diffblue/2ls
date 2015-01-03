#include <iostream>

#include <util/simplify_expr.h>
#include "strategy_solver_predabs.h"

#define DEBUG_OUTPUT

bool strategy_solver_predabst::iterate(invariantt &_inv) 
{
  predabs_domaint::templ_valuet &inv = 
    static_cast<predabs_domaint::templ_valuet &>(_inv);

  worklistt::iterator e_it = todo_preds.begin();
  if(e_it != todo_preds.end()) //check positive preds
    {
      solver.new_context();
      exprt preinv_expr = predabs_domain.get_row_pre_constraint(*e_it, true_exprt());

#ifdef DEBUG_OUTPUT
      debug() << "pre-pred: " << from_expr(ns,"",preinv_expr) << eom;
#endif

      solver << preinv_expr;
    
      exprt strategy_cond_expr;
      strategy_cond_expr = predabs_domain.get_row_post_constraint(*e_it, true_exprt()); 

      literalt cond_literal = solver.solver.convert(not_exprt(strategy_cond_expr));
      solver << literal_exprt(cond_literal);

#ifdef DEBUG_OUTPUT
      debug() << "post-pred: " << from_expr(ns,"",not_exprt(strategy_cond_expr)) << eom;
#endif


      if(solver() == decision_proceduret::D_SATISFIABLE) 
	{ 
	  debug() << "SAT" << eom;

#if 0         
	  for(replace_mapt::const_iterator
		it=predabs_domain.renaming_map.begin();
	      it!=predabs_domain.renaming_map.end();    
	      ++it)
	  {
	    debug() << "replace_map (1st): " << 
	      from_expr(ns, "", it->first) << " " <<
	      from_expr(ns, "", solver.solver.get(it->first)) << eom;
	    debug() << "replace_map (2nd): " << from_expr(ns, "", it->second) << " " 
		    << from_expr(ns, "", solver.solver.get(it->second)) << eom;
	  }
#endif
	  todo_notpreds.insert(*e_it);

	  solver.pop_context();

	}
      else 
	{

	  debug() << "UNSAT" << eom;

	  predabs_domain.set_row_value(*e_it, true_exprt(), inv);

	  solver.pop_context();

	  solver << preinv_expr; //make permanent

	  //due to transitivity, we would like to recheck predicates that did not hold
	  todo_preds.insert(todo_notpreds.begin(),todo_notpreds.end());
	  todo_notpreds.clear();
	}

      todo_preds.erase(e_it);

      return true;
    }

  return false;
}
