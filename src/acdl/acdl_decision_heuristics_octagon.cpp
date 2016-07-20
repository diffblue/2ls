/*******************************************************************\

Module: ACDL Decision Heuristics

Author: Rajdeep Mukherjee, Peter Schrammel

\*******************************************************************/
#include <limits.h>
#include <fstream>
#include <cstdlib>
#include "acdl_solver.h"
#include "acdl_decision_heuristics_octagon.h"

#define DEBUG 1

acdl_domaint::meet_irreduciblet acdl_decision_heuristics_octagont::operator()
(const local_SSAt &SSA, const acdl_domaint::valuet &value)
{
#ifdef DEBUG
  std::cout << "Printing all decision variables" << std::endl;
  for(std::set<exprt>::const_iterator 
    it = decision_variables.begin(); it != decision_variables.end(); ++it)
      std::cout << from_expr(SSA.ns, "", *it) << "  ," << std::endl;
#endif
  
  bool decision=false;    
  std::string strc("cond");
  exprt val;
  std::string name;
  std::vector<exprt> conds;
  std::vector<exprt> non_cond;
  std::set<symbol_exprt> non_cond_sym;

  // copy the decision_variables in separate vector
  for(std::set<exprt>::const_iterator 
    it = decision_variables.begin(); it != decision_variables.end(); ++it) 
  {
    const irep_idt &identifier = it->get(ID_identifier);
    name = id2string(identifier);
    std::size_t found = name.find(strc);
    if(found!=std::string::npos) 
      conds.push_back(*it);
    else {
      non_cond.push_back(*it);
      acdl_domaint::varst sym;
      find_symbols(*it, sym);
      non_cond_sym.insert(sym.begin(), sym.end());
    }
  }
    
  // 1> pick a cond variable
  // 2> check if it is singleton
  // 3> If not singleton, return it.
  bool cond=false;
  for(int i=0;i<conds.size();i++) {
    const acdl_domaint::meet_irreduciblet 
      exp = conds[i];
    val = domain.split(value, exp);
    if(!val.is_false()) {
      cond=true; 
      return val; 
    }
  }

  // cond set must be exhausted
  assert(cond==false);
  // get the templates 
  std::vector<exprt> templates;
  std::cout << "Printing the symbols before building template" << std::endl;
  for(std::set<symbol_exprt>::iterator it = non_cond_sym.begin(); it != non_cond_sym.end(); it++)
    std::cout << from_expr(SSA.ns, "", *it) << std::endl; 
  
  // call template generator
  domain.build_meet_irreducible_templates(non_cond_sym, templates); 
  std::vector<bool> non_cond_marked(templates.size(), true);

#ifdef DEBUG
  std::cout << "Printing the templates" << std::endl;
  std::cout << "Total number of templates :" << templates.size() << std::endl;
  for(int i=0;i<templates.size();i++) 
    std::cout << from_expr(SSA.ns, "", templates[i]) << std::endl;
#endif 
  
  while(!decision) {
    // make decisions on non-cond variables
    assert(templates.size() != 0);
    unsigned index = rand() % templates.size();
    const acdl_domaint::meet_irreduciblet cexp = 
      templates[index];
    // this variable is already singleton  
    if(non_cond_marked[index]==false) continue; 
    val = domain.split(value, cexp);
    if(!val.is_false()) {
      decision=true; 
      return val; 
    }
    else { 
      non_cond_marked[index]=false;
      continue;
    }
  }

  assert(!decision && !cond);
#ifdef DEBUG
    std::cout << "No decisions can be made" << std::endl;
#endif       
  
}
