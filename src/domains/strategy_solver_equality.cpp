#include <iostream>

#include <util/simplify_expr.h>
#include "strategy_solver_equality.h"

bool strategy_solver_equalityt::iterate(invariantt &_inv) 
{
  equality_domaint::equ_valuet &inv = 
    static_cast<equality_domaint::equ_valuet &>(_inv);

  worklistt::iterator e_it = todo_equs.begin();
  if(e_it!=todo_equs.end()) //check equalities
  {
    literalt activation_literal = new_context();

    exprt pre_expr = equality_domain.get_pre_equ_constraint(*e_it);

    solver << or_exprt(pre_expr,literal_exprt(activation_literal));
    
    exprt post_expr = equality_domain.get_post_not_equ_constraint(*e_it);
    rename(post_expr);
    literalt cond_literal = solver.convert(post_expr);

    solver << or_exprt(literal_exprt(cond_literal),
                       literal_exprt(activation_literal));

    debug() << "Checking equality " << eom;
    debug() << "Pre: " << from_expr(ns, "", pre_expr) << eom;
    debug() << "Post: " << from_expr(ns, "", post_expr) << eom;

    if(solver() == decision_proceduret::D_SATISFIABLE) 
    { 
      debug() << "SAT" << eom;
      todo_disequs.insert(*e_it);
    }
    else  //equality holds
    {
      debug() << "UNSAT" << eom;
      
      equality_domain.set_equal(*e_it,inv);
      solver << pre_expr; //make permanent
    }

    pop_context();

    todo_equs.erase(e_it);

    //check status of remaining equalities
    /*   worklistt rm_equs;
    for(e_it = todo_equs.begin(); e_it!=todo_equs.end(); e_it++)
    {
      equality_domaint::var_pairt vv = equality_domain.get_var_pair(*e_it);
      if(solver.get(vv.first)!=solver.get(vv.second))
        rm_equs.insert(*e_it);
    }
    for(e_it = rm_equs.begin(); e_it!=rm_equs.end(); e_it++)
    {
      todo_disequs.insert(*e_it);
      todo_equs.erase(*e_it);
      } */
  }
  else //check disequalities
  {
    e_it = todo_disequs.begin();
    if(e_it==todo_disequs.end()) return false; //done

    literalt activation_literal = new_context();

    exprt pre_expr = equality_domain.get_pre_disequ_constraint(*e_it);

    solver << or_exprt(pre_expr,literal_exprt(activation_literal));
    
    exprt post_expr = equality_domain.get_post_not_disequ_constraint(*e_it);
    rename(post_expr);
    literalt cond_literal = solver.convert(post_expr);

    solver << or_exprt(literal_exprt(cond_literal),
                       literal_exprt(activation_literal));

    debug() << "Checking disequality " << eom;
    debug() << "Pre: " << from_expr(ns, "", pre_expr) << eom;
    debug() << "Post: " << from_expr(ns, "", post_expr) << eom;

    if(solver() == decision_proceduret::D_SATISFIABLE) 
    { 
      debug() << "SAT" << eom;
    }
    else  //equality holds
    {
      debug() << "UNSAT" << eom;
      
      equality_domain.set_disequal(*e_it,inv);
      solver << pre_expr; //make permanent
    }

    pop_context();

    todo_disequs.erase(e_it);
  }

  return true;
}
