#include <iostream>

#include <util/simplify_expr.h>
#include "lexlinrank_solver_enumeration.h"

#define DEBUG_FORMULA 
#define MAX_ELEMENTS 2 // lexicographic components
#define MAX_OUTER_ITERATIONS 20


bool lexlinrank_solver_enumerationt::iterate(invariantt &_rank)
{
  lexlinrank_domaint::templ_valuet &rank = 
    static_cast<lexlinrank_domaint::templ_valuet &>(_rank);

  bool improved = false;
  static std::vector<int> number_elements_per_row;
  number_elements_per_row.resize(rank.size());

  //static int number_outer_iterations;
  //number_outer_iterations = 0;

  debug() << "(RANK) no rows = " << rank.size() << eom;

  // instantiate the "inner" solver
  //satcheck_minisat_no_simplifiert satcheck1;
  //bv_pointerst inner_solver(ns, satcheck1);

  literalt activation_literal = new_context();

  //handles on values to retrieve from model
  std::vector<lexlinrank_domaint::pre_post_valuest> rank_value_exprs;
  exprt::operandst rank_cond_exprs;
  bvt rank_cond_literals;

  exprt rank_expr = lexlinrank_domain.get_not_constraints(rank, rank_cond_exprs, rank_value_exprs);

#ifndef DEBUG_FORMULA
  solver << or_exprt(rank_expr, literal_exprt(activation_literal));
#else
  debug() << "(RANK) Rank constraint : " << from_expr(ns,"",rank_expr) << eom; 
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

  
    for(unsigned row = 0; row < rank_cond_literals.size(); row++)
    {
      // retrieve values from the model x_i and x'_i
      lexlinrank_domaint::pre_post_valuest values;
  
      if(solver.l_get(rank_cond_literals[row]).is_true()) 
      {
	for(lexlinrank_domaint::pre_post_valuest::iterator it = rank_value_exprs[row].begin(); 
	    it != rank_value_exprs[row].end(); ++it) 
       {
	  // model for x_i
	  exprt value = solver.get(it->first);
	  debug() << "(RANK) Row " << row << " Value for " << from_expr(ns,"",it->first) 
		  << ": " << from_expr(ns,"",value) << eom;
	  // model for x'_i
	  exprt post_value = solver.get(it->second);
	  debug() << "(RANK) Row " << row << " Value for " << from_expr(ns,"",it->second) 
		  << ": " << from_expr(ns,"",post_value) << eom;
	  // record all the values
	  values.push_back(std::make_pair(value, post_value));
	}

	lexlinrank_domaint::row_valuet symb_values;
        symb_values.resize(rank[row].size());

	debug() << "elements: " << rank[row].size() << eom;

	exprt constraint;
	exprt refinement_constraint;

	// generate the new constraint
	constraint = lexlinrank_domain.get_row_symb_constraint(symb_values, row, values, refinement_constraint);

	simplify_expr(constraint, ns);
	debug() << "Inner Solver: " << row << " constraint " 
		    << from_expr(ns,"", constraint) << eom;

	inner_solver << constraint;

	debug() << "inner solve()" << eom;

        //set assumptions for refinement
        bvt assumptions;
        if(refinement_constraint.is_true()) assumptions.resize(0); //no assumptions
        else
	{
          assumptions.resize(1);
          assumptions[0] = inner_solver.convert(refinement_constraint);
	}	

	//debug() << "LALALA" << eom;
        inner_solver.set_assumptions(assumptions);

	// solve
	if(inner_solver() == decision_proceduret::D_SATISFIABLE && 
	   number_outer_iterations < MAX_OUTER_ITERATIONS) 
	{ 

	  number_outer_iterations++;
	  
	  debug() << "(RANK) inner solver: number of outer refinements = " << number_outer_iterations << eom;
	  debug() << "(RANK) inner solver: number of components for row " << row << " is " << number_elements_per_row[row] << eom;
	  debug() << "(RANK) inner solver: SAT" << eom;

	  // new_row_values will contain the new values for c and d
	  lexlinrank_domaint::row_valuet new_row_values;
          new_row_values.resize(rank[row].size());

	  for(unsigned constraint_no = 0; constraint_no < symb_values.size(); ++constraint_no) {

	    std::vector<exprt> c = symb_values[constraint_no].c;


	    // get the model for all c
	    for(std::vector<exprt>::iterator it = c.begin(); it != c.end(); ++it) 
	      {
		exprt v = inner_solver.get(*it);
		new_row_values[constraint_no].c.push_back(v);
		debug() << "Inner Solver: " << row << " c value for " 
			<< from_expr(ns,"", *it) << ": " 
			<< from_expr(ns,"", v)  << eom;
	      }

	    // get the model for d
	    // new_row_values[constraint_no].d = inner_solver.get(symb_values[constraint_no].d);
	    // debug() << "Inner Solver: " << row << " d value for " 
	    // 	    << from_expr(ns,"", symb_values[constraint_no].d)<< ": " 
	    // 	    << from_expr(ns,"", new_row_values[constraint_no].d)  << eom;

	  }

	  improved = true;

	  // update the current template
	  lexlinrank_domain.set_row_value(row, new_row_values, rank);

	}
	else {
	  debug() << "(RANK) inner solver: UNSAT or reached max number of outer refinements" << eom;

	  if(number_elements_per_row[row] == MAX_ELEMENTS-1) {
	    debug() << "(RANK) reached the max no of refinements and no ranking function was found" << eom;
	    // no ranking function for the current template
	    lexlinrank_domain.set_row_value_to_true(row, rank);
	  }
	  else {
	    debug() << "(RANK) inner solver: reached max number of outer refinements" << eom;
	    lexlinrank_domain.add_element(row, rank);
	    number_outer_iterations = 0;
	    number_elements_per_row[row]++;
	    debug() << "(RANK) the no of refinements for row " << row << " was increased to " << number_elements_per_row[row] << eom;
	    improved = true;
	  }
	}
      }
    }

  }
  else 
    {
      debug() << "(RANK) outer solver: UNSAT" << eom;
    }

  pop_context();

  return improved;
}
