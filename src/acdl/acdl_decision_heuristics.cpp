/*******************************************************************\

Module: ACDL Decision Heuristics

Author: Rajdeep Mukherjee, Peter Schrammel

\*******************************************************************/
#include <limits.h>
#include <fstream>
#include <cstdlib>
#include "acdl_solver.h"
#include "acdl_decision_heuristics.h"

#define DEBUG 1

acdl_domaint::meet_irreduciblet acdl_decision_heuristicst::operator()
(const local_SSAt &SSA, const acdl_domaint::valuet &value)
{
  dec_heur = RAND;
  switch(dec_heur)
  {
    case BERKMIN:
      return dec_heur_berkmin(SSA, value);
      break;
    case RANGE:
      return dec_heur_largest_range(SSA, value, false);
      break;
    case RANGE_REL:
      return dec_heur_largest_range(SSA, value, true);
      break;
    case RAND:
      return dec_heur_rand(SSA, value);
      break;
    default:
      throw "impossible";
  } 
}


/*******************************************************************

 Function: acdl_solvert::dec_heur_rand()

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

acdl_domaint::meet_irreduciblet acdl_decision_heuristicst::dec_heur_rand
      (const local_SSAt &SSA, const acdl_domaint::valuet &value)
{
#ifdef DEBUG
  std::cout << "Printing all decision variables" << std::endl;
  for(std::set<exprt>::const_iterator 
    it = decision_variables.begin(); it != decision_variables.end(); ++it)
      std::cout << from_expr(SSA.ns, "", *it) << "  ," << std::endl;
#endif
  // collect the non-singleton variables
  std::vector<exprt> non_singletons;
  std::vector<exprt> singletons;
  acdl_domaint::meet_irreduciblet val;
  for(std::set<exprt>::const_iterator 
    it = decision_variables.begin(); it != decision_variables.end(); ++it) {
    val = domain.split(value, *it);
    if(!val.is_false()) 
      non_singletons.push_back(val);
   // collect all singleton variables 
   else
     singletons.push_back(*it);
  }
  
  // pop the decision variables which 
  // are already singletons
  for(std::vector<exprt>::const_iterator 
    it = singletons.begin(); it != singletons.end(); ++it) 
     decision_variables.erase(decision_variables.find(*it)); 
  
   // no more decisions can be made
   if(non_singletons.size() == 0) {
#ifdef DEBUG
     std::cout << "[FALSE DECISION] " << "FALSE" << std::endl;
#endif
     return false_exprt();
   }

#ifdef DEBUG
  std::cout << "Printing all non-singletons decision variables" << std::endl;
  for(std::vector<exprt>::const_iterator 
    it = non_singletons.begin(); it != non_singletons.end(); ++it)
      std::cout << from_expr(SSA.ns, "", *it) << "  ," << std::endl;
#endif

  std::vector<exprt> non_cond;
  std::vector<exprt> cond;
  std::string str("cond");
  std::string name;
  // separate the non-singleton cond and non_cond variables
  for(std::vector<exprt>::const_iterator 
      it = non_singletons.begin(); it != non_singletons.end(); ++it) { 
    // check if it is not of type x<=10 or x>=10 but 
    // something like !cond or cond
    const exprt &e = *it;
    if(e.id() != ID_le && e.id() != ID_ge && e.id() != ID_lt && e.id() != ID_gt)
    {
      exprt exp = it->op0();
      const irep_idt &identifier = exp.get(ID_identifier);
      name = id2string(identifier);
      std::size_t found = name.find(str);
      if (found!=std::string::npos) 
        cond.push_back(*it);
      //cond.push_back(*it);
    }
    else   
      non_cond.push_back(*it);
  }
  
  // Make a decision
  if(cond.size() == 0) {
    // select non-cond decision variables
    const acdl_domaint::meet_irreduciblet dec_expr_rand = 
      non_cond[rand() % non_cond.size()];
#ifdef DEBUG
    std::cout << "[NON-COND DECISION] " << dec_expr_rand << std::endl;
#endif
    return dec_expr_rand;
  }
  else {
    // select cond decision variables
    const acdl_domaint::meet_irreduciblet dec_expr_rand = 
      cond[rand() % cond.size()];
#ifdef DEBUG
    std::cout << "[COND DECISION] " << dec_expr_rand << std::endl;
#endif
    return dec_expr_rand;
  }
        
    
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
#if 0
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
  if(eligible_vars.size() == 0) {
    return false_exprt();
    // check for non-cond decision variables
    // use complete random decision heuristics from all 
    // non-singleton decision variables
    const acdl_domaint::meet_irreduciblet dec_expr_rand = 
    non_singletons[rand() % non_singletons.size()];
    return dec_expr_rand;
  }
  
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
#endif
    
}


/*******************************************************************

 Function: acdl_solvert::dec_heur_largest_range()

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

acdl_domaint::meet_irreduciblet acdl_decision_heuristicst::dec_heur_largest_range
  (const local_SSAt &SSA, const acdl_domaint::valuet &value, bool phase)
{
  acdl_domaint::meet_irreduciblet decision;
  return decision;
}

/*******************************************************************

 Function: acdl_solvert::dec_heur_berkmin()

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

acdl_domaint::meet_irreduciblet acdl_decision_heuristicst::dec_heur_berkmin(const local_SSAt &SSA, const acdl_domaint::valuet &value)
{
  acdl_domaint::meet_irreduciblet decision;
  return decision;
}
