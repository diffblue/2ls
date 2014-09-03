#include <iostream>

#include <util/simplify_expr.h>
#include "ranking_solver_enumeration.h"
#include <solvers/sat/satcheck.h>
#include <solvers/flattening/bv_pointers.h>



bool ranking_solver_enumerationt::iterate(invariantt &_rank)
{
  linrank_domaint::templ_valuet &rank = 
    static_cast<linrank_domaint::templ_valuet &>(_rank);

  bool improved = false;

  literalt activation_literal = new_context();

  //handles on values to retrieve from model
  linrank_domaint::pre_post_valuest rank_value_exprs;
  exprt::operandst rank_cond_exprs;
  bvt rank_cond_literals;

  exprt rank_expr = linrank_domain.get_not_constraints(rank, rank_cond_exprs, rank_value_exprs);

  solver << or_exprt(rank_expr, literal_exprt(activation_literal));

  rank_cond_literals.resize(rank_cond_exprs.size());
  
  for(unsigned i = 0; i < rank_cond_exprs.size(); i++)
  {  
    rank_cond_literals[i] = solver.convert(rank_cond_exprs[i]);
    rank_cond_exprs[i] = literal_exprt(rank_cond_literals[i]);
  }

  debug() << "solve(): ";


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
	  // model for x'_i
	  exprt post_value = solver.get(it->second);
	  // record all the values
	  values.push_back(std::make_pair(value, post_value));
	}

	linrank_domaint::row_valuet row_values;
	exprt constraint;

	// generate the new constraint
	constraint = linrank_domain.get_row_symb_contraint(row_values, row, values);
	literalt activation_literal1 = new_context();

	// instantiate a new solver
	satcheck_minisat_no_simplifiert satcheck;
	bv_pointerst solver1(ns, satcheck);

	solver1 << or_exprt(constraint, literal_exprt(activation_literal1));

	if(solve() == decision_proceduret::D_SATISFIABLE) { 

	  std::vector<exprt> c = row_values.c;

	  // new_row_values will contain the new values for c and d
	  linrank_domaint::row_valuet new_row_values;

	  // get the model for all c
	  for(std::vector<exprt>::iterator it = c.begin(); it != c.end(); ++it) {
	    exprt v = solver1.get(*it);
	    new_row_values.c.push_back(v);
	  }

	  // get the model for d
	  new_row_values.d = solver1.get(row_values.d);

	  // update the current template
	  linrank_domain.set_row_value(row, new_row_values, rank);

	  improved = true;
	}
	else {
	  debug() << "Second solver: UNSAT" << eom;
	}

	pop_context();
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
