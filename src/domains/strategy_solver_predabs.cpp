#include <iostream>

#include <util/simplify_expr.h>
#include "strategy_solver_predabs.h"

bool strategy_solver_predabst::iterate(invariantt &_inv) 
{
  predabs_domaint::templ_valuet &inv = 
    static_cast<predabs_domaint::templ_valuet &>(_inv);

  bool improved = false;
  literalt activation_literal = new_context();

  exprt pre_expr = predabs_domain.to_pre_constraints(inv);

  solver << or_exprt(pre_expr,literal_exprt(activation_literal));
    
  exprt::operandst strategy_cond_exprs;
  predabs_domain.make_not_post_constraints(inv, 
    strategy_cond_exprs); 
  
  strategy_cond_literals.resize(strategy_cond_exprs.size());
  
  debug() << "post-inv: ";
  for(unsigned i = 0; i<strategy_cond_exprs.size(); i++)
  {  
    debug() << (i>0 ? " || " : "") << from_expr(ns,"",strategy_cond_exprs[i]) ;

    strategy_cond_literals[i] = solver.convert(strategy_cond_exprs[i]);
    strategy_cond_exprs[i] = literal_exprt(strategy_cond_literals[i]);
  }
  debug() << eom;

  solver << or_exprt(disjunction(strategy_cond_exprs),
		     literal_exprt(activation_literal));

  if(solve() == decision_proceduret::D_SATISFIABLE) 
  { 
    debug() << "SAT" << eom;
    for(unsigned row=0;row<strategy_cond_literals.size(); row++)
    {
      if(solver.l_get(strategy_cond_literals[row]).is_true()) 
      {
        debug() << "updating row: " << row << eom;
        predabs_domain.set_row_value(row,true_exprt(),inv);
      }
    }
    improved = true;
  }
  else 
  {
    debug() << "UNSAT" << eom;
  }

  pop_context();

  return improved;
}
