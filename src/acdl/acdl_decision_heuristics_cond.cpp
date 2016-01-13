/*******************************************************************\

Module: ACDL Decision Heuristics (Branch on Condition Variables)

Author: Rajdeep Mukherjee, Peter Schrammel

\*******************************************************************/

#include "acdl_decision_heuristics_cond.h"

acdl_domaint::meet_irreduciblet acdl_decision_heuristics_condt::operator()
(const local_SSAt &SSA, const acdl_domaint::valuet &value)
{
  exprt decision_expr; //TODO: This characterize the shape of the decisions made, (eg. x < 5 or x-y < 5)
  exprt decision_var;
  acdl_domaint::valuet decision; // container that contains the decision (eg. x == [0,10])
  
  //TODO
  // use information from VSIDS to choose decision 'variable'
  
  // ***********************************************************************
  // Note: using CFG flow instead can be used to emulate a forward analysis
  //       This is similar to Astree simulation 
  // ***********************************************************************

  // choose a meet irreducible
  // 1. pick possible decision from source code 
  
  // *******************************************
  // 1.a. look at conditions in the SSA: cond#3
  //      decision = cond_var
  // *******************************************
  std::string str("cond");
  std::string lhs_str;
  conds cond_container;
  for (local_SSAt::nodest::const_iterator n_it = SSA.nodes.begin ();
      n_it != SSA.nodes.end (); n_it++)
  {
    for (local_SSAt::nodet::equalitiest::const_iterator e_it =
        n_it->equalities.begin (); e_it != n_it->equalities.end (); e_it++)
    {
      const irep_idt &identifier = e_it->lhs().get(ID_identifier);
      // check if the rhs of an equality is a constant, 
      // in that case don't do anything  
      if(e_it->rhs().id() == ID_constant) {}
      else {
        lhs_str = id2string(identifier); //e_it->lhs().get(ID_identifier)); 
        std::size_t found = lhs_str.find(str);
        if (found!=std::string::npos) {
#ifdef DEBUG
        std::cout << "DECISION PHASE: " << from_expr (SSA.ns, "", e_it->lhs()) << std::endl;
#endif        
          //decision_var = e_it->lhs();
          // store the conditional variables in a container
          cond_container.push_back(e_it->lhs()); 
        }
      }
    }
  }
  // For conditional based decision heuristics, 
  // decision expressions are same as decision variables in split function
  decision=false_exprt();
  for(std::list<exprt>::const_iterator it = cond_container.begin(); it != cond_container.end(); ++it)
  {
    decision_var = *it;
    decision_expr = decision_var;

    decision = domain.split(decision_var,decision_expr,1);
    if(decision.is_false()) {
      continue;
    }
    std::cout << "DECISION SPLITTING VALUE: " << from_expr (SSA.ns, "", decision) << std::endl;
  }
#if 0  
  equal_exprt dec_expr(decision_var, decision);
  std::cout << "DECISION SPLITTING EXPR: " << from_expr (SSA.ns, "", dec_expr) << std::endl;
#endif
  // if decision heuristic return false, no decision has been made
  return decision;
}
