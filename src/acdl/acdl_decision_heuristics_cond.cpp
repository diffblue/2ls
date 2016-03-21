/*******************************************************************\

Module: ACDL Decision Heuristics (Branch on Condition Variables)

Author: Rajdeep Mukherjee, Peter Schrammel

\*******************************************************************/
#include <limits.h>
#include <fstream>
#include <cstdlib>
#include "acdl_decision_heuristics_cond.h"

acdl_domaint::meet_irreduciblet acdl_decision_heuristics_condt::operator()
(const local_SSAt &SSA, const acdl_domaint::valuet &value)
{
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
  dec_pair d;
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
          d.first = e_it->lhs();       
          d.second = *e_it;
          cond_container.push_back(d); 
        }
      }
    }
  }
  // For conditional based decision heuristics, 
  // First collect all decision variables which are not singletons
  //std::vector<acdl_domaint::meet_irreduciblet> eligible_vars;
  std::vector<dec_pair> eligible_vars;
  acdl_domaint::meet_irreduciblet dec;
  /*for(std::list<exprt>::const_iterator itc = cond_container.begin();
      itc != cond_container.end(); ++itc) */

  for(std::list<dec_pair>::const_iterator itc = cond_container.begin();
      itc != cond_container.end(); ++itc)
  {
    const exprt &decision_expr = itc->first;
    dec = domain.split(value,decision_expr);
    if(!dec.is_false()) 
      eligible_vars.push_back(*itc);
  }
  // no more decisions can be made
  if(eligible_vars.size() == 0)
    return false_exprt();
  
  //int index = rand() % eligible_vars.size();
  const dec_pair &v1 = eligible_vars[rand() % eligible_vars.size()];
  //const dec_pair &v1 = eligible_vars[index];
  const exprt &v = v1.first;
  dec_statement = v1.second;
  //const exprt &v = eligible_vars[rand() % eligible_vars.size()];
 
 
  // decision expressions are same as decision variables in split function
  acdl_domaint::meet_irreduciblet decision = false_exprt();
  decision = domain.split(value,v,true);
  
  //dec_trail.push_back(decision);
#if 0
  for(std::list<exprt>::const_iterator it = cond_container.begin();
      it != cond_container.end(); ++it)
  {
    //This characterize the shape of the decisions made, (eg. x < 5 or x-y < 5)
    const exprt &decision_expr = *it;
    decision = domain.split(value,decision_expr,true);
    if(!decision.is_false()) 
      break;
  }
  std::cout << "DECISION SPLITTING VALUE: " << from_expr (SSA.ns, "", decision) << std::endl;
#endif 
  return decision;
}
