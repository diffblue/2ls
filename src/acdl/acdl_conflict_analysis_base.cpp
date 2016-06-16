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
bool acdl_conflict_analysis_baset::chronological_backtrack(const local_SSAt &SSA, 
                    acdl_implication_grapht &graph)
{
  if(graph.current_level == 0) {
    backtrack_level = -1; // no further backtrack possible
    return false;
  }
  // otherwise get decision element
  // must return a meet irreducible 
  acdl_domaint::meet_irreduciblet expr = graph.dec_trail.back(); 
  // backtrack one level
  cancel_once(SSA, graph);
  
  // negate the expression
  exprt exp = flip(expr);
  // insert new decision element into dec_trail
  graph.dec_trail.push_back(exp);
  graph.add_decision(exp);
  
  
  // update the backtrack level
  backtrack_level = graph.current_level;
  just_backtracked = true;
  
  // check graph consistency
  graph.check_consistency(graph.current_level);
  return true;
}

  
/*******************************************************************\

Function: acdl_conflict_analysis_baset::operator()

  Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/
bool acdl_conflict_analysis_baset::operator()
  (const local_SSAt &SSA, acdl_implication_grapht &graph, acdl_domaint::valuet &conf_clause)
{
  // abstract dpll strategy, no clause learning
  if(disable_backjumping) {
    return(chronological_backtrack(SSA, graph)); 
  }
   
  //conflict_clauset conf_clause;
  get_conflict_clause(SSA, graph, conf_clause);
 
  // no further backtrack possible
  if(backtrack_level < 0) {
    //property_checkert::resultt result = property_checkert::PASS;
    //return result;
    return false;
  }
  
  // add the conflict clause to the learned clause database
  // learned_clauses.push_back(conf_clause);
  
  // backtrack
  cancel_until(SSA,graph,backtrack_level);

#ifdef DEBUG
  std::cout << "backtrack to dlevel: " << backtrack_level << std::endl;
#endif  
  
  backtracks++;
  
  // check that the clause is unit
  //assert(unit_rule(conflict_clause));
  
  
  just_backtracked = true;

  // check graph consistency
  graph.check_consistency(backtrack_level);
  return true;  
}


/*******************************************************************\

Function: acdl_conflict_analysis_baset::get_conflict_clause()

  Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/
 
void acdl_conflict_analysis_baset::get_conflict_clause
  (const local_SSAt &SSA, acdl_implication_grapht &graph, acdl_domaint::valuet &conf_clause)
{
  if(graph.current_level == 0) {
    backtrack_level = -1;
  }
  else 
  {
    exprt expr;
    // find the uip from graph
    int uip = graph.first_uip(SSA);
    
    acdl_domaint::valuet reason; 
    // find the reason for conflict through graph cutting
    graph.get_reason(uip, reason); 
    // construct the conflict clause
    // by negating each element of reason
    int max_reason_dl = -1;
    for(acdl_domaint::valuet::const_iterator it = reason.begin();
        it != reason.end(); it++)
    {
      acdl_domaint::meet_irreduciblet exp = *it;
      expr = flip(exp);
      conf_clause.push_back(expr);
      // backtrack_level = max{level(x) : x is an element of conf_clause - p}
      // where p is one literal of conf_clause assigned at conflict level (uip)
      // note that reason does not contain the uip
      int idx = graph.find_node(exp);  
      if(graph.decision_level(idx) > max_reason_dl)
        max_reason_dl = graph.decision_level(idx);
    }
    // now push the negation of the uip node
    // into the conflict clause
    exprt uip_expr = graph.find_node_expr(uip);
    conf_clause.push_back(flip(uip_expr));
    
    // print the learned clause
    std::cout << "The learned clause is: " << conjunction(conf_clause) << std::endl;
    // check if the size of conflict clause is zero
    if(conf_clause.size() == 0)
      backtrack_level = -1;
    else {
      // uip is the only reason for conflict,
      // this can happen when chosing the last uip
      // which is the decision node itself
      if(max_reason_dl == -1) 
       max_reason_dl = 0; 
       //max_reason_dl = graph.decision_level(uip);
      backtrack_level = max_reason_dl; 
    }
  }
}

/*******************************************************************\

Function: acdl_conflict_analysis_baset::cancel_until()

  Inputs:

 Outputs:

 Purpose: backtracks by several level

 \*******************************************************************/
void acdl_conflict_analysis_baset::cancel_until
   (const local_SSAt &SSA, acdl_implication_grapht &graph, int lvl) 
{
  while(graph.current_level > lvl)
     cancel_once(SSA,graph);
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
  //graph.remove_out_edges(na);
  std::cout << "****************************" << std::endl;
  std::cout << "Deleting out nodes" << std::endl;
  std::cout << "****************************" << std::endl;
  graph.delete_out_nodes(na);
  
  // remove everything starting from the conflicting node (identified by
  // false_exprt()  
  int nb = graph.find_node(false_exprt());
  std::cout << "The false_exprt node is: " << nb << std::endl;
  std::cout << "****************************" << std::endl;
  std::cout << "Deleting in nodes" << std::endl;
  std::cout << "****************************" << std::endl;
  graph.delete_in_nodes(nb);
  //graph.remove_in_edges(nb);
  // mark nodes of graph as deleted
  graph.delete_graph_nodes(); 
  
  // unmark the nodes in the graph 
  // to prepare it for next iteration
  graph.unmark_nodes();
  graph.current_level--;
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
