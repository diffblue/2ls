/*******************************************************************\

Module: ACDL Decision Heuristics

Author: Rajdeep Mukherjee, Peter Schrammel

\*******************************************************************/
#include <limits.h>
#include <fstream>
#include <cstdlib>
#include "acdl_solver.h"
#include "acdl_decision_heuristics_berkmin.h"

#define DEBUG 1

/*******************************************************************\

Function: acdl_domaint::berkmin()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
acdl_domaint::meet_irreduciblet acdl_decision_heuristics_berkmint::operator()
(const local_SSAt &SSA, const acdl_domaint::valuet &value)
{
#ifdef DEBUG
  std::cout << "Printing all decision variables" << std::endl;
  for(std::set<exprt>::const_iterator 
    it = decision_variables.begin(); it != decision_variables.end(); ++it)
      std::cout << from_expr(SSA.ns, "", *it) << "  ," << std::endl;
#endif
  
  int num_clauses = conflict_analysis.learned_clauses.size();
  std::vector<acdl_domaint::meet_irreduciblet> unsat_lits;
  unsigned contradicted=0;
  int i;
  
  // copy the value to non-constant value
  acdl_domaint::valuet v;
  for(int k=0;k<value.size();k++)
    v.push_back(value[k]);
  domain.normalize(v); 
  
  // iterate over all learned clauses 
  // and find the unsat literal for decision
  for(i=num_clauses-1;i>=0;i--) 
  {
    acdl_domaint::valuet clause = conflict_analysis.learned_clauses[i];
#ifdef DEBUG
    std::cout << "checking clause" << from_expr(SSA.ns, "", disjunction(clause)) << std::endl;
#endif    
    assert(clause.size()!=0);
    for(int j=0;j<clause.size();j++)
    {
      exprt clause_exp = clause[j];
#ifdef DEBUG
      std::cout << "checking literal" << clause_exp << std::endl;
#endif      
      unsigned status = domain.compare_val_lit(v, clause_exp);
      if(status!=2) // not SATISFIED
      {
        if(status!=0) // not contradicted
          unsat_lits.push_back(clause_exp);
        else 
          ++contradicted;
      }
    }

    assert(contradicted < clause.size()); //otherwise we'd have a contradicted clause

    if(unsat_lits.size() > 0);
    break;
  }
  bool decision=false;
  while(!decision) {
    if(unsat_lits.size() != 0) {
      std::cout << "Berkmin heuristics: Choosing unsat literal from clause" 
        << i << "of" << num_clauses << std::endl;

      exprt chosen_lit = unsat_lits[rand() % unsat_lits.size()];

      exprt flipped_literal;
      // invert it randomly
      if(rand() & 1)
      {
        flipped_literal = conflict_analysis.flip(chosen_lit);
      }
      // check the consistency 
      // of the decision 
      //not sure if v has to be unnormalized  
      unsigned status = domain.compare_val_lit(v, flipped_literal); 
      if(status != 0) { // not conflicting
        decision=true;
        return flipped_literal;
      }
      else {
        continue;
        //bad_decision.push_back(flipped_literal);   
      }
    }
    else
    {
      std::cout << "No clause with unsat lits found. Choosing randomly" << std::endl;
      return(random_dec_heuristics(SSA, value));
    }
  }
}    
    
    
/*******************************************************************\

Function: acdl_domaint::random_dec_heuristic()

 Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
acdl_domaint::meet_irreduciblet acdl_decision_heuristics_berkmint::random_dec_heuristics
(const local_SSAt &SSA, const acdl_domaint::valuet &value)
{
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
        decision=true;
        cond=true; 
        return val; 
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
      decision=true; 
      return val; 
    }
    else { 
      // mark the non_cond that is already singleton
      non_cond_marked[index]=false;
      continue;  
    }
  }
}
