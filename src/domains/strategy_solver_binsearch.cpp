#include <iostream>

#include "strategy_solver_binsearch.h"
#include "util.h"

// #define DEBUG_FORMULA

bool strategy_solver_binsearcht::iterate(invariantt &_inv)
{
  tpolyhedra_domaint::templ_valuet &inv = 
    static_cast<tpolyhedra_domaint::templ_valuet &>(_inv);

  bool improved = false;

  solver.new_context(); //for improvement check

  exprt inv_expr = tpolyhedra_domain.to_pre_constraints(inv);

#if 0
  debug() << "improvement check: " << eom;
  debug() << "pre-inv: " << from_expr(ns,"",inv_expr) << eom;
#endif

  solver << inv_expr;

  exprt::operandst strategy_cond_exprs;
  tpolyhedra_domain.make_not_post_constraints(inv, 
    strategy_cond_exprs, strategy_value_exprs); 
  
  strategy_cond_literals.resize(strategy_cond_exprs.size());
  
#if 0
  debug() << "post-inv: ";
#endif
  for(unsigned i = 0; i<strategy_cond_exprs.size(); i++)
  {  
#if 0
    debug() << (i>0 ? " || " : "") << from_expr(ns,"",strategy_cond_exprs[i]);
#endif
    strategy_cond_literals[i] = solver.solver.convert(strategy_cond_exprs[i]);
    //solver.set_frozen(strategy_cond_literals[i]);
    strategy_cond_exprs[i] = literal_exprt(strategy_cond_literals[i]);
  }
  debug() << eom;

  solver << disjunction(strategy_cond_exprs);

#if 0
  debug() << "solve(): ";
#endif

#ifdef DEBUG_FORMULA
  bvt whole_formula = formula;
  whole_formula.insert(whole_formula.end(),activation_literals.begin(),
                       solver.activation_literals.end());
  solver.solver.set_assumptions(whole_formula);
#endif

  if(solver() == decision_proceduret::D_SATISFIABLE) //improvement check
  { 
#if 0
    debug() << "SAT" << eom;
#endif
      
#if 0
    for(unsigned i=0; i<whole_formula.size(); i++) 
    {
      debug() << "literal: " << whole_formula[i] << " " << 
        solver.solver.l_get(whole_formula[i]) << eom;
    }
          
    for(unsigned i=0; i<tpolyhedra_domain.template_size(); i++) 
    {
      exprt c = tpolyhedra_domain.get_row_constraint(i,inv[i]);
      debug() << "cond: " << from_expr(ns, "", c) << " " << 
	    from_expr(ns, "", solver.get(c)) << eom;
      debug() << "guards: " << 
        from_expr(ns, "", tpolyhedra_domain.templ.pre_guards[i]) << 
        " " << from_expr(ns, "", 
          solver.solver.get(tpolyhedra_domain.templ.pre_guards[i])) << eom;
      debug() << "guards: " << from_expr(ns, "", 
          tpolyhedra_domain.templ.post_guards[i]) << " " 
	  << from_expr(ns, "", 
             solver.solver.get(tpolyhedra_domain.templ.post_guards[i])) << eom;
    }    
#endif

   
    unsigned row=0;  
    for(;row<strategy_cond_literals.size(); row++)
    {
      if(solver.solver.l_get(strategy_cond_literals[row]).is_true()) 
        break;  // we've found a row to improve
    }

    debug() << "improving row: " << row << eom;
    std::set<tpolyhedra_domaint::rowt> improve_rows;
    improve_rows.insert(row);

    tpolyhedra_domaint::row_valuet upper = 
      tpolyhedra_domain.get_max_row_value(row);
    tpolyhedra_domaint::row_valuet lower = 
      //  tpolyhedra_domain.get_min_row_value(row);
    simplify_const(solver.solver.get(strategy_value_exprs[row]));

    solver.pop_context();  //improvement check
    
    solver.new_context(); //symbolic value system

    exprt pre_inv_expr = 
      tpolyhedra_domain.to_symb_pre_constraints(inv,improve_rows);

    solver << pre_inv_expr;

    exprt post_inv_expr = tpolyhedra_domain.get_row_symb_post_constraint(row);

    solver << post_inv_expr;

#if 0
    debug() << "symbolic value system: " << eom;
    debug() << "pre-inv: " << from_expr(ns,"",pre_inv_expr) << eom; 
    debug() << "post-inv: " << from_expr(ns,"",post_inv_expr) << eom;
#endif

    while(tpolyhedra_domain.less_than(lower,upper))   
    {
      tpolyhedra_domaint::row_valuet middle = 
	      tpolyhedra_domain.between(lower,upper);
      if(!tpolyhedra_domain.less_than(lower,middle)) middle = upper;

      // row_symb_value >= middle
      exprt c = tpolyhedra_domain.get_row_symb_value_constraint(row,middle);

#if 0
      debug() << "upper: " << from_expr(ns,"",upper) << eom;
      debug() << "middle: " << from_expr(ns,"",middle) << eom;
      debug() << "lower: " << from_expr(ns,"",lower) << eom;
#endif

      solver.new_context(); // binary search iteration

#if 0
      debug() << "constraint: " << from_expr(ns, "", c) << eom;
#endif

      solver << c;

#ifdef DEBUG_FORMULA
      bvt whole_formula = formula;
      whole_formula.insert(whole_formula.end(),activation_literals.begin(),
                       activation_literals.end());
      solver.solver.set_assumptions(whole_formula);
#endif

      if(solver() == decision_proceduret::D_SATISFIABLE) 
      { 
#if 0
	debug() << "SAT" << eom;
#endif
	
#if 0
      for(unsigned i=0; i<tpolyhedra_domain.template_size(); i++) 
      {
        debug() <<  
          from_expr(ns, "", tpolyhedra_domain.get_row_symb_value(i)) << " " << 
	  from_expr(ns, "", solver.solver.get(tpolyhedra_domain.get_row_symb_value(i))) 
          << eom;
      }
#endif

#if 0          
      for(replace_mapt::const_iterator
	    it=renaming_map.begin();
          it!=renaming_map.end();    
          ++it)
      {
	  debug() << "replace_map (1st): " << 
            from_expr(ns, "", it->first) << " " <<
	    from_expr(ns, "", solver.solver.get(it->first)) << eom;
	  debug() << "replace_map (2nd): " << from_expr(ns, "", it->second) << " " 
		  << from_expr(ns, "", solver.get(it->second)) << eom;
      }
#endif
      
      	lower = middle;
      }
      else 
      {
#if 0
	debug() << "UNSAT" << eom;
#endif

#ifdef DEBUG_FORMULA
	for(unsigned i=0; i<whole_formula.size(); i++) 
        {
	  if(solver.solver.is_in_conflict(whole_formula[i]))
	      debug() << "is_in_conflict: " << whole_formula[i] << eom;
	  else
	      debug() << "not_in_conflict: " << whole_formula[i] << eom;
        }
#endif

        if(!tpolyhedra_domain.less_than(middle,upper)) middle = lower;

	upper = middle;
      }
      solver.pop_context(); // binary search iteration
    }
   
#if 1
    debug() << "update value: " << from_expr(ns,"",lower) << eom;
#endif

    solver.pop_context();  //symbolic value system

    tpolyhedra_domain.set_row_value(row,lower,inv);
    improved = true;
  }
  else 
  {
#if 0
    debug() << "UNSAT" << eom;
#endif

    solver.pop_context(); //improvement check
  }

  
  return improved;
}
