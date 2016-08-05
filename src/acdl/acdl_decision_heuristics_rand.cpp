/*******************************************************************\

Module: ACDL Decision Heuristics

Author: Rajdeep Mukherjee, Peter Schrammel

\*******************************************************************/
#include <limits.h>
#include <fstream>
#include <cstdlib>
#include "acdl_solver.h"
#include "acdl_decision_heuristics_rand.h"

#define DEBUG 1

acdl_domaint::meet_irreduciblet acdl_decision_heuristics_randt::operator()
(const local_SSAt &SSA, const acdl_domaint::valuet &value)
{
#ifdef DEBUG
  std::cout << "Printing all decision variables" << std::endl;
  for(std::set<exprt>::const_iterator 
    it = decision_variables.begin(); it != decision_variables.end(); it++)
      std::cout << from_expr(SSA.ns, "", *it) << "  ," << std::endl;
#endif
  
  // copy the value to non-constant value
  acdl_domaint::valuet v;
  for(int k=0;k<value.size();k++)
    v.push_back(value[k]);
  
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
  
  // [TODO] Do not pop decision variables since it 
  // is possible that a decision has to be made on 
  // a singleton variable after backtracking when it 
  // is no more a singleton variable.
  /*for(std::vector<exprt>::const_iterator 
    it = singletons.begin(); it != singletons.end(); ++it) 
     decision_variables.erase(decision_variables.find(*it)); 
  */

   // no more decisions can be made
   if(non_singletons.size() == 0) {
#ifdef DEBUG
     std::cout << "NO DECISIONS CAN BE MADE " << std::endl;
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
  
  bool decision=false; 
  // Make a decision
  while(!decision) {
    if(cond.size() == 0) {
#if 0
      // choose non-cond decision variables that 
      // are nondet-vars 
      // choose input nondet variables
      if(nondet_var.size()>0) {
        const acdl_domaint::meet_irreduciblet dec_expr_nondet = 
          nondet_var[rand() % nondet_var.size()];
        // now search for nondet_vars that are not singletons
        acdl_domaint::varst sym1;
        find_symbols(dec_expr_nondet, sym1);
        for(int i=0;i<non_cond.size();i++) {
          acdl_domaint::varst sym2;
          find_symbols(non_cond[i], sym2);
          for(acdl_domaint::varst::iterator it1 = sym2.begin(); it1 != sym2.end(); it1++) {
            bool is_in = sym1.find(*it1) != sym1.end();
            if(is_in) 
              return non_cond[i]; 
          }
        }
      }
#endif
      // select non-cond decision variables
      acdl_domaint::meet_irreduciblet dec_expr_rand = 
        non_cond[rand() % non_cond.size()];
#ifdef DEBUG
      std::cout << "[NON-COND DECISION] " << dec_expr_rand << std::endl;
#endif
      unsigned status = domain.compare_val_lit(v, dec_expr_rand); 
      if(status != 0) { // not conflicting
        decision=true;
        return dec_expr_rand;
      }
      else 
        continue;
    }
    else {
      // select cond decision variables
      acdl_domaint::meet_irreduciblet dec_expr_rand = 
        cond[rand() % cond.size()];
#ifdef DEBUG
      std::cout << "[COND DECISION] " << dec_expr_rand << std::endl;
#endif
      unsigned status = domain.compare_val_lit(v, dec_expr_rand); 
      if(status != 0) { // not conflicting
        decision=true;
        return dec_expr_rand;
      }
      else 
        continue;
    }
  }
}
