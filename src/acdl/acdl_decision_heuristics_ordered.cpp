/*******************************************************************\

Module: ACDL Decision Heuristics

Author: Rajdeep Mukherjee, Peter Schrammel

\*******************************************************************/
#include <limits.h>
#include <fstream>
#include <cstdlib>
#include "acdl_solver.h"
#include "acdl_decision_heuristics_ordered.h"

// #define DEBUG 

acdl_domaint::meet_irreduciblet acdl_decision_heuristics_orderedt::operator()
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
  
  bool decision=false;    
  std::string strc("cond");
  exprt val;
  std::string name;
  std::vector<exprt> conds;
  std::vector<exprt> non_cond;

  // copy the decision_variables in separate vector
  for(std::set<exprt>::const_iterator 
    it = decision_variables.begin(); it != decision_variables.end(); ++it) 
  {
    const irep_idt &identifier = it->get(ID_identifier);
    name = id2string(identifier);
    std::size_t found = name.find(strc);
    if(found!=std::string::npos) 
      conds.push_back(*it);
    else
      non_cond.push_back(*it);
  }
  //initialize the vectors with true
  std::vector<bool> conds_marked(conds.size(), true);
  std::vector<bool> non_cond_marked(non_cond.size(), true);

  while(!decision) {
    bool cond_dec_left=false;
    bool non_cond_dec_left=false;
    // make decisions only if 
    // there are non-singletons 
    for(int j=0;j<conds.size();j++) {
      if(conds_marked[j] != false) {
        cond_dec_left = true;
      }
    }
    for(int k=0;k<non_cond.size();k++) {
      if(non_cond_marked[k] != false) {
        non_cond_dec_left = true;
      }
    }
    if(!cond_dec_left && !non_cond_dec_left) {
#ifdef DEBUG
     std::cout << "NO DECISIONS CAN BE MADE " << std::endl;
#endif
     return false_exprt();
   }

    // assert there are some non-singletons 
    assert(cond_dec_left || non_cond_dec_left);
    // 1> pick a variable randomly
    // 2> check if it is a cond variable and singleton
    // 3> If not singleton, return it.
    bool cond=false;
    for(int i=0;i<conds.size();i++) {
      const acdl_domaint::meet_irreduciblet 
           exp = conds[i];
      val = domain.split(value, exp);
      if(!val.is_false()) {
       unsigned status = domain.compare_val_lit(v, val);
       if(status != 0) {
         decision=true;
         cond=true; 
         return val; 
       }
       else 
         continue; 
     }
     else {
       // mark the cond that is already singleton
       conds_marked[i]=false;
     }
    }
    // assert that the cond set is exhausted
    assert(cond==false);
    
    // make decisions on non-cond variables
    unsigned index = rand() % non_cond.size();
    const acdl_domaint::meet_irreduciblet cexp = 
      non_cond[index];
    // this variable is already singleton  
    if(non_cond_marked[index]==false) continue; 
    val = domain.split(value, cexp);
    if(!val.is_false()) {
      unsigned status = domain.compare_val_lit(v, val);
      if(status != 0) {
       decision=true; 
       return val; 
      }
      else
       continue;
    }
    else { 
      // mark the non_cond that is already singleton
      non_cond_marked[index]=false;
      continue;  
    }
  }
}
