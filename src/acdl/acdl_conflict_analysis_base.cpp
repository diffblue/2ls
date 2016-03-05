/*******************************************************************\

Module: ACDL Clause Learning Base

Author: Rajdeep Mukherjee, Peter Schrammel

 \*******************************************************************/

#include <util/find_symbols.h>
#include "acdl_conflict_analysis_base.h"

/*******************************************************************\

Function: acdl_conflict_analysis_baset::backtrack_to_level

  Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/
void acdl_conflict_analysis_baset::backtrack_to_level(acdl_implication_grapht &graph,
						      unsigned int idx)
{
  
}

/*******************************************************************\

Function: abstr_dpll_searcht::chronological_backtrack
 
  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
/*
bool acdl_conflict_analysis_baset::chronological_backtrack(abstr_elementt& elem)
{
  if(graph.current_level == 0)
    backtrack_level = -1; //no further backtrack possible

  //otherwise get decision element
  unsigned first_idx = control_trail.back();
  assert(var_trail.size() >= first_idx + 1);
  
  literalt dec_lit = lit_from_trail(first_idx);

  cancel_once();

  flip(dec_lit);
  
  assign(dec_lit);

  elem = 
    itv_array_domain.from_itv_assignments(numbering, values);
  
  just_backtracked = true;
  return true;
}
*/  
/*******************************************************************\

Function: acdl_conflict_analysis_baset::operator()

  Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/
  
  
property_checkert::resultt acdl_conflict_analysis_baset::operator()
             (acdl_implication_grapht &graph, exprt &learned_clause)
{
  // abstract dpll strategy, no clause learning
  /*if(disable_backjumping) {
    chronological_backtrack(); 
    // no further backtrack possible
    if(backtrack_level < 0) {
      property_checkert::resultt result = property_checkert::PASS;
      return result;
    }
    else 
    {
      property_checkert::resultt result = property_checkert::UNKNOWN;
      return result;
    }
  }*/
  
   
  acdl_domaint::meet_irreduciblet conflict_clause;

  get_conflict_clause(graph, conflict_clause);
  
  // no further backtrack possible
  if(backtrack_level < 0) {
    property_checkert::resultt result = property_checkert::PASS;
    return result;
  }
  
  // add the conflict clause to the learned 
  // clause database
  //add_clause(conflict_clause);
  
  // backtrack
  //cancel_until(backtrack_level);

#ifdef DEBUG
  std::cout << "backtrack to dlevel: " << graph.current_level << std::endl;
#endif  
  
  backtracks++;
  
  // check that the clause is unit
  //assert(unit_rule(conflict_clause));
  
  
  just_backtracked = true;
  
  property_checkert::resultt result = property_checkert::PASS;
    return result;
  //return true;  
  // check that the added clause  
#if 0
  if(graph.current_level == 0) {
    backtrack_level = -1;
    property_checkert::resultt result = property_checkert::PASS;
    return result;
  }
  else 
  {
    learn_and_backtrack(graph);
    // assert(false);
  }
#endif
}


/*******************************************************************\

Function: acdl_conflict_analysis_baset::get_conflict_clause()

  Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/
 
void acdl_conflict_analysis_baset::get_conflict_clause(acdl_implication_grapht &graph, acdl_domaint::meet_irreduciblet &clause)
{
  if(graph.current_level == 0) {
    backtrack_level = -1;
  }
  else 
  {
    //learn_and_backtrack(graph);
    assert(false);
  }
  
  //assert(false);
}

