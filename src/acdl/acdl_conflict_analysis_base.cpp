/*******************************************************************\

Module: ACDL Clause Learning Base

Author: Rajdeep Mukherjee, Peter Schrammel

\*******************************************************************/

#include <util/find_symbols.h>
#include "acdl_conflict_analysis_base.h"

#define DEBUG

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
  if(graph.current_level==0) {
    backtrack_level=-1; // no further backtrack possible
    return false;
  }
  // otherwise get decision element
  // must return a meet irreducible
  acdl_domaint::meet_irreduciblet expr=graph.dec_trail.back();
  exprt dec_exp=expr;
  // backtrack one level
  cancel_once(SSA, graph, dec_exp);

  // negate the expression
  exprt exp=flip(expr);
  // insert new decision element into dec_trail
  graph.dec_trail.push_back(exp);
  graph.add_decision(exp);


  // update the backtrack level
  backtrack_level=graph.current_level;
  just_backtracked=true;

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

  // conflict_clauset conf_clause;
  get_conflict_clause(SSA, graph, conf_clause);

  // no further backtrack possible
  if(backtrack_level<0) {
    return false;
  }

  // add the conflict clause to the learned clause database
  // learned_clauses.push_back(conf_clause);

  // backtrack
  std::cout << "****************" << std::endl;
  std::cout << "BACKTRACK PHASE" << std::endl;
  std::cout << "****************" << std::endl;
#ifdef DEBUG
  std::cout << "backtrack to dlevel: " << backtrack_level << std::endl;
#endif
  cancel_until(SSA, graph, backtrack_level);

  backtracks++;

  // check that the clause is unit
  // assert(unit_rule(conflict_clause));

  just_backtracked=true;
#ifdef DEBUG
  std::cout << "Successfully backtracked" << std::endl;
#endif

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
  if(graph.current_level==0) {
    backtrack_level=-1;
  }
  else
  {
    exprt expr;
    int uip=0;
    // find the uip from graph
#if 0
    int uip=graph.first_uip(SSA);
#endif
    acdl_domaint::valuet reason;
    // find the reason for conflict through graph cutting
    graph.get_reason(SSA, uip, reason);
    // construct the conflict clause
    // by negating each element of reason
    int max_reason_dl=-1;
    int node_dec_level=-1;
    for(acdl_domaint::valuet::const_iterator it=reason.begin();
        it!=reason.end(); it++)
    {
      acdl_domaint::meet_irreduciblet exp=*it;
      int nidx=graph.find_node(*it);
      // this check is only when the
      // learned clause involves all decisions
      // and without uip (Armin Biere CDCL tutorial)
      // if(nodes[nidx].is_decision && nodes[nidx].dec_level.back()==current_level)
      //  continue;
      expr=flip(exp);
      conf_clause.push_back(expr);
      // backtrack_level=max{level(x) : x is an element of conf_clause-p}
      // where p is one literal of conf_clause assigned at conflict level (uip)
      // note that reason does not contain the uip
      int idx=graph.find_node(exp);
      node_dec_level=graph.search_node__dec_level(idx);
      if(node_dec_level > max_reason_dl)
        max_reason_dl=node_dec_level;
      #if 0
      if(graph.decision_level(idx) > max_reason_dl)
       max_reason_dl=graph.decision_level(idx);
      #endif
    }
    // now push the negation of the uip node
    // into the conflict clause
#if 0
    exprt uip_expr=graph.find_node_expr(uip);
    conf_clause.push_back(flip(uip_expr));
#endif

    // normalize the decision
    domain.normalize_val(conf_clause);
    // print the learned clause
#ifdef DEBUG
    std::cout << "The learned clause is: " << from_expr(SSA.ns, "", conjunction(conf_clause)) << std::endl;
#endif
    // check if the size of conflict clause is zero
    if(conf_clause.size()==0)
      backtrack_level=-1;
    else {
      // uip is the only reason for conflict,
      // this can happen when chosing the last uip
      // and the conflict clause contains only the uip
      // which is the decision node itself
      if(max_reason_dl==-1)
       max_reason_dl=0;
       // max_reason_dl=graph.decision_level(uip);
      backtrack_level=max_reason_dl;
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
  // copy the decision trail
  acdl_implication_grapht::decision_trail temp_dec_trail;
  temp_dec_trail.assign(graph.dec_trail.begin(), graph.dec_trail.end());
  // the dec_trail size must not be less than
  // the total number of backtrackings to be done
  assert(!(temp_dec_trail.size()<(graph.current_level-lvl)));
  while(graph.current_level > lvl) {
     exprt dec_exp=temp_dec_trail.back();
     temp_dec_trail.pop_back();
     cancel_once(SSA, graph, dec_exp);
  }

  // mark nodes of graph as deleted
  graph.delete_graph_nodes();

  std::cout << "***********************************************" << std::endl;
  std::cout << "IMPLICATION GRAPH AFTER FINAL BACKTRACKING" << std::endl;
  std::cout << "***********************************************" << std::endl;
  graph.print_graph_output(SSA);

  // unmark the nodes in the graph
  // to prepare it for next iteration
  graph.unmark_nodes();
}
/*******************************************************************\

Function: acdl_conflict_analysis_baset::cancel_once()

  Inputs:

 Outputs:

 Purpose: backtracks by one level

 \*******************************************************************/
void acdl_conflict_analysis_baset::cancel_once(const local_SSAt &SSA, acdl_implication_grapht &graph, exprt& expr)
{
  // const exprt expr=graph.dec_trail.;
  std::cout << "cancelling deductions corresponding to decision node: " << from_expr(SSA.ns, "", expr) << std::endl;
  // remove everything starting from the present decision node
  int na=graph.find_node(expr);
  // this can happen when decision node
  // has already been deleted because it
  // did not contribute to any deductions
  // The situation under which this can trigger
  // is when we do multiple backtracking until
  // we reach a non-conflict state (do-while loop in solver)
  if(na==-1) {
    graph.adjust_decision_level();
    graph.current_level--;
    return;
  }

  // assert(na!=-1);
  // graph.remove_out_edges(na);
  std::cout << "****************************" << std::endl;
  std::cout << "Deleting out nodes" << std::endl;
  std::cout << "****************************" << std::endl;
  graph.delete_out_nodes(na);

  // remove everything starting from the conflicting node (identified by
  // false_exprt()
  int nb=graph.find_node(false_exprt());
  std::cout << "The false_exprt node is: " << nb << std::endl;
  std::cout << "****************************" << std::endl;
  std::cout << "Deleting in nodes" << std::endl;
  std::cout << "****************************" << std::endl;
  graph.delete_in_nodes(nb);
  // graph.remove_in_edges(nb);
  graph.print_graph_output(SSA);

  graph.adjust_decision_level();
  graph.current_level--;
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
