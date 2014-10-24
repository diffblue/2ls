#include <iostream>

#include <util/simplify_expr.h>
#include "lexlinrank_solver_enumeration.h"
#include "util.h"

#define DEBUG_INNER_FORMULA 
#define MAX_ELEMENTS 3 // lexicographic components
#define MAX_REFINEMENTS 20

bool lexlinrank_solver_enumerationt::iterate(invariantt &_rank)
{
  lexlinrank_domaint::templ_valuet &rank = 
    static_cast<lexlinrank_domaint::templ_valuet &>(_rank);

  bool improved = false;
  static std::vector<int> number_elements_per_row;
  number_elements_per_row.resize(rank.size());

  debug() << "(RANK) no rows = " << rank.size() << eom;

  solver.new_context();

  //handles on values to retrieve from model
  std::vector<lexlinrank_domaint::pre_post_valuest> rank_value_exprs;
  exprt::operandst rank_cond_exprs;
  bvt rank_cond_literals;

  exprt rank_expr = lexlinrank_domain.get_not_constraints(rank, 
    rank_cond_exprs, rank_value_exprs);

  solver << rank_expr;

  rank_cond_literals.resize(rank_cond_exprs.size());
  for(unsigned i = 0; i < rank_cond_exprs.size(); i++)
  {  
    rank_cond_literals[i] = solver.solver.convert(rank_cond_exprs[i]);
  }

  debug() << "solve(): ";

#ifdef DEBUG_FORMULA
  bvt whole_formula = formula;
  whole_formula.insert(whole_formula.end(),activation_literals.begin(),activation_literals.end());
  solver.set_assumptions(whole_formula);
#endif

#if 0
  // check whether the literal is UNSAT to start with
  satcheck_minisat_no_simplifiert test_satcheck;
  bv_pointerst test_solver = bv_pointerst(ns, test_satcheck);

  test_solver << rank_expr;

  if(test_solver() == decision_proceduret::D_SATISFIABLE)
    debug() << "test solver: SAT" << eom;
  else
    debug() << "test solver: UNSAT" << eom;
#endif

  if(solver() == decision_proceduret::D_SATISFIABLE) 
  { 
    debug() << "(RANK) outer solver: SAT" << eom;

    for(unsigned row = 0; row < rank_cond_literals.size(); row++)
    {
      // retrieve values from the model x_i and x'_i
      lexlinrank_domaint::pre_post_valuest values;
  
      if(solver.solver.l_get(rank_cond_literals[row]).is_true()) 
      {
	for(lexlinrank_domaint::pre_post_valuest::iterator it = 
	      rank_value_exprs[row].begin(); 
	    it != rank_value_exprs[row].end(); ++it) 
	{
	  // model for x_i
	  exprt value = solver.solver.get(it->first);
	  debug() << "(RANK) Row " << row << " Value for " 
		  << from_expr(ns,"",it->first) 
		  << ": " << from_expr(ns,"",value) << eom;
	  // model for x'_i
	  exprt post_value = solver.solver.get(it->second);
	  debug() << "(RANK) Row " << row << " Value for " 
		  << from_expr(ns,"",it->second) 
		  << ": " << from_expr(ns,"",post_value) << eom;
	  // record all the values
	  values.push_back(std::make_pair(value, post_value));
	}

	lexlinrank_domaint::row_valuet symb_values;
        symb_values.resize(rank[row].size());

	//debug() << "elements: " << rank[row].size() << eom;

	exprt constraint;
	exprt refinement_constraint;

	// generate the new constraint
	constraint = lexlinrank_domain.get_row_symb_constraint(symb_values, 
          row, values, refinement_constraint);

	simplify_expr(constraint, ns);
	debug() << "(RANK) Constraint sent to the inner Solver: " << row 
		<< " constraint ";
	pretty_print_termination_argument(debug(), ns, constraint);
 
	debug() << eom;


#ifndef DEBUG_INNER_FORMULA
	*inner_solver << constraint;

        //set assumptions for refinement
        bvt assumptions;
        if(refinement_constraint.is_true()) assumptions.resize(0); //no assumptions
        else
	{
          assumptions.resize(1);
          assumptions[0] = inner_solver->solver.convert(refinement_constraint);
	}	

        inner_solver->solver.set_assumptions(assumptions);

#else
	literalt inner_l = inner_solver->solver.convert(constraint);
	debug() << "(RANK-inner) literal " << inner_l 
		<< " corresponds to formula ";
	pretty_print_termination_argument(debug(), ns, constraint); 	
	debug() << eom;

	if(!inner_l.is_constant()) 
	{
	  inner_formula.push_back(inner_l);
	}

        //set assumptions for refinement
        if(!refinement_constraint.is_true()) {
	  literalt refinement_l = 
	    inner_solver->solver.convert(refinement_constraint);
	  debug() << "(RANK-inner) literal " << refinement_l 
		  << " corresponds to refinement formula ";
	  pretty_print_termination_argument(debug(), ns, refinement_constraint)	; debug() << eom;
	  inner_formula.push_back(refinement_l);
	}	

	inner_solver->solver.set_assumptions(inner_formula);

#endif
	debug() << "(RANK) inner solve()" << eom;
	// solve
	//decision_proceduret::
	bool inner_solver_result = (*inner_solver)(); 
	if(inner_solver_result == decision_proceduret::D_SATISFIABLE && 
	   number_refinements < MAX_REFINEMENTS) 
	{ 
	  number_refinements++;
	  
	  debug() << "(RANK) inner solver: SAT and the max number of refinements was not reached " << eom;
	  debug() << "(RANK) inner solver: Current number of refinements = " << number_refinements << eom;
	  debug() << "(RANK) inner solver: Current number of components for row " << row << " is " << number_elements_per_row[row]+1 << eom;

	  // new_row_values will contain the new values for c and d
	  lexlinrank_domaint::row_valuet new_row_values;
          new_row_values.resize(rank[row].size());

	  for(unsigned constraint_no = 0; constraint_no < symb_values.size(); ++constraint_no) {

	    std::vector<exprt> c = symb_values[constraint_no].c;

	    // get the model for all c
	    for(std::vector<exprt>::iterator it = c.begin(); it != c.end(); ++it) 
	    {
	      exprt v = inner_solver->solver.get(*it);
	      new_row_values[constraint_no].c.push_back(v);
	      debug() << "(RANK) Inner Solver: row " << row 
		      << " ==> c value for ";
	      pretty_print_termination_argument(debug(), ns, *it); 
	      debug() << ": "; 
	      pretty_print_termination_argument(debug(), ns, v);
	      debug() << eom;
	    }
	  }

	  improved = true;

	  // update the current template
	  lexlinrank_domain.set_row_value(row, new_row_values, rank);

	}
	else 
	{
	  if(inner_solver_result == decision_proceduret::D_UNSATISFIABLE)
	    debug() << "(RANK) inner solver: UNSAT" << eom;
	  else
	    debug() << "(RANK) inner solver: reached max number of refinements" << eom;

	  debug() << "(RANK) inner solver: number of refinements = " << number_refinements << eom;

#ifdef DEBUG_INNER_FORMULA
	  for(unsigned i=0; i<inner_formula.size(); i++) 
	  {
	    if(inner_solver->solver.is_in_conflict(inner_formula[i]))
	      debug() << "(RANK-inner) is_in_conflict: " << inner_formula[i] << eom;
	    else
	      debug() << "(RANK-inner) not_in_conflict: " << inner_formula[i] << eom;
	  }
#endif    

	  if(lexlinrank_domain.refine()) 
	  {
	    debug() << "refining..." << eom;
	    improved = true; //refinement possible
	  }
	  else
	  {
	    if(number_elements_per_row[row] == MAX_ELEMENTS-1) {
	      debug() << "(RANK) reached the max no of lexicographic components and no ranking function was found" << eom;
	      // no ranking function for the current template
	      lexlinrank_domain.set_row_value_to_true(row, rank);
	    }
	    else {
	      number_elements_per_row[row]++;
	      debug() << "(RANK) inner solver: increasing the number of lexicographic componenets for row " << row << " to " << number_elements_per_row[row] + 1 << eom;
	      // reset the inner solver
	      debug() << "(RANK) reset the inner solver " << eom;
	      delete inner_solver;
	      inner_solver = new incremental_solvert(ns);
	      inner_formula.clear();
	      lexlinrank_domain.reset_refinements();

	      lexlinrank_domain.add_element(row, rank);
	      number_refinements = 0;
	      debug() << "(RANK) inner solver: the number of refinements for row " << row << " was reset to " << number_refinements << eom;
	      improved = true;
	    }
	  }
	}
      }
    }

  }
  else 
  {
    debug() << "(RANK) outer solver: UNSAT!!" << eom;
#ifdef DEBUG_OUTER_FORMULA
    for(unsigned i=0; i<formula.size(); i++) {
      if(solver.solver.is_in_conflict(formula[i]))
	debug() << "(RANK-outer) is_in_conflict: " << formula[i] << eom;
      else
	debug() << "(RANK-outer) not_in_conflict: " << formula[i] << eom;
    }
#endif    


  }

  solver.pop_context();
  debug() << "(RANK): outer solver => pop context" << eom;
  return improved;
}
