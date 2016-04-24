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
void acdl_conflict_analysis_baset::chronological_backtrack(const local_SSAt &SSA, acdl_implication_grapht &graph)
{
  if(graph.current_level == 0) {
    backtrack_level = -1; //no further backtrack possible
    return;
  }
  // otherwise get decision element
  // must return a meet irreducible 
  acdl_domaint::meet_irreduciblet expr = graph.dec_trail.back(); 
  cancel_once(SSA, graph);

  exprt exp = flip(expr);
  // insert new decision element into dec_trail
  graph.dec_trail.push_back(exp);
  graph.add_decision(exp);
  
  graph.current_level--;
  // update the backtrack level
  backtrack_level = graph.current_level;
  just_backtracked = true;
  //return true;
}
  
/*******************************************************************\

Function: acdl_conflict_analysis_baset::operator()

  Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/
property_checkert::resultt acdl_conflict_analysis_baset::operator()
             (const local_SSAt &SSA, acdl_implication_grapht &graph, exprt &learned_clause)
{
  // abstract dpll strategy, no clause learning
  if(disable_backjumping) {
    chronological_backtrack(SSA, graph); 
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
  }
   
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
 
void acdl_conflict_analysis_baset::get_conflict_clause
  (acdl_implication_grapht &graph, acdl_domaint::meet_irreduciblet &clause)
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

/*******************************************************************\

Function: acdl_conflict_analysis_baset::cancel_once()

  Inputs:

 Outputs:

 Purpose: backtracks by one level

 \*******************************************************************/
void acdl_conflict_analysis_baset::cancel_once(const local_SSAt &SSA, acdl_implication_grapht &graph) 
{
  const exprt expr = graph.dec_trail.back();  

  // remove everything starting from the present decision node
  int na = graph.find_node(expr);
  graph.remove_out_edges(na);
  // remove everything starting from the conflicting node (identified by
  // false_exprt()  
  int nb = graph.find_node(false_exprt());
  std::cout << "The false_exprt node is: " << nb << std::endl;
  graph.remove_in_edges(nb);
  graph.delete_graph_nodes(); 

  std::cout << "***********************************************" << std::endl;
  std::cout << "IMPLICATION GRAPH AFTER BACKTRACKING" << std::endl;
  std::cout << "***********************************************" << std::endl;
  graph.print_graph_output(SSA);
}

/*******************************************************************\

Function: acdl_conflict_analysis_baset::flip()

  Inputs:

 Outputs:

 Purpose: flip present meet irreducible

 \*******************************************************************/
exprt acdl_conflict_analysis_baset::flip(acdl_domaint::meet_irreduciblet &m) 
{
  not_exprt not_exp(m); 
  return not_exp;
}
