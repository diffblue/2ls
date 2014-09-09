#include <iostream>

#include <util/simplify_expr.h>
#include "ranking_solver_enumeration.h"
#include <solvers/sat/satcheck.h>
#include <solvers/flattening/bv_pointers.h>

#define DEBUG_FORMULA 

bool ranking_solver_enumerationt::iterate(invariantt &_rank)
{
  linrank_domaint::templ_valuet &rank = 
    static_cast<linrank_domaint::templ_valuet &>(_rank);

  bool improved = false;

  // instantiate the "inner" solver
  satcheck_minisat_no_simplifiert satcheck1;
  bv_pointerst solver1(ns, satcheck1);

  literalt activation_literal = new_context();

  //handles on values to retrieve from model
  linrank_domaint::pre_post_valuest rank_value_exprs;
  exprt::operandst rank_cond_exprs;
  bvt rank_cond_literals;

  exprt rank_expr = linrank_domain.get_not_constraints(rank, rank_cond_exprs, rank_value_exprs);

#ifndef DEBUG_FORMULA
  solver << or_exprt(rank_expr, literal_exprt(activation_literal));
#else
  debug() << "(RANK) Rank constraint : " << rank_expr << eom; 
  debug() << "(RANK) literal " << activation_literal << eom;
  literalt l = solver.convert(or_exprt(rank_expr, literal_exprt(activation_literal)));
  if(!l.is_constant()) 
  {
    debug() << "(RANK) literal " << l << ": " << from_expr(ns,"",or_exprt(rank_expr, literal_exprt(activation_literal))) <<eom;
    formula.push_back(l);
  }
#endif



  rank_cond_literals.resize(rank_cond_exprs.size());
  
  for(unsigned i = 0; i < rank_cond_exprs.size(); i++)
  {  
    rank_cond_literals[i] = solver.convert(rank_cond_exprs[i]);
    rank_cond_exprs[i] = literal_exprt(rank_cond_literals[i]);
  }

  debug() << "solve(): ";

#ifdef DEBUG_FORMULA
  bvt whole_formula = formula;
  whole_formula.insert(whole_formula.end(),activation_literals.begin(),activation_literals.end());
  solver.set_assumptions(whole_formula);
#endif

  if(solve() == decision_proceduret::D_SATISFIABLE) 
  { 
    debug() << "SAT" << eom;

    // retrieve values from the model x_i and x'_i
    linrank_domaint::pre_post_valuest values;
  
    for(unsigned row = 0; row < rank_cond_literals.size(); row++)
    {
      if(solver.l_get(rank_cond_literals[row]).is_true()) 
      {
	for(linrank_domaint::pre_post_valuest::iterator it = rank_value_exprs.begin(); it != rank_value_exprs.end(); ++it) {
	  // model for x_i
	  exprt value = solver.get(it->first);
	  debug() << "(RANK) Value for " << it->first << ": " << value << eom;
	  // model for x'_i
	  exprt post_value = solver.get(it->second);
	  debug() << "(RANK) Value for " << it->second << ": " << post_value << eom;
	  // record all the values
	  values.push_back(std::make_pair(value, post_value));
	}

	linrank_domaint::row_valuet symb_values;
	exprt constraint;




	// generate the new constraint
	constraint = linrank_domain.get_row_symb_contraint(symb_values, row, values);

	solver1 << constraint;

	if(solver1() == decision_proceduret::D_SATISFIABLE) { 

	  std::vector<exprt> c = symb_values.c;

	  // new_row_values will contain the new values for c and d
	  linrank_domaint::row_valuet new_row_values;

	  // get the model for all c
	  for(std::vector<exprt>::iterator it = c.begin(); it != c.end(); ++it) {
	    exprt v = solver1.get(*it);
	    new_row_values.c.push_back(v);
	  }

	  // get the model for d
	  new_row_values.d = solver1.get(symb_values.d);

	  // update the current template
	  linrank_domain.set_row_value(row, new_row_values, rank);

	  improved = true;
	}
	else {
	  debug() << "Second solver: UNSAT" << eom;
	}
      }
    }

  }
  else 
  {
    debug() << "UNSAT" << eom;

  }

  pop_context();

  return improved;
}
