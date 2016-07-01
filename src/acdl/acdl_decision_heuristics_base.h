/*******************************************************************\

Module: ACDL Decision Heuristics Interface

Author: Rajdeep Mukherjee, Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_ACDL_DECISION_HEURISTICS_BASE_H
#define CPROVER_ACDL_DECISION_HEURISTICS_BASE_H

#include <goto-programs/property_checker.h>

#include "acdl_domain.h"
#include "../ssa/local_ssa.h"

class acdl_decision_heuristics_baset : public messaget
{
public:
  
  explicit acdl_decision_heuristics_baset(
    acdl_domaint &_domain)
    : 
  domain(_domain)
  {
  }  

  virtual ~acdl_decision_heuristics_baset() 
  {
  }
  
  //override this
  virtual acdl_domaint::meet_irreduciblet operator()(
    const local_SSAt &SSA,
    const acdl_domaint::valuet &value)
  {
    assert(false);
  }
  
  acdl_domaint::statementt dec_statement;
  std::set<exprt> decision_variables;
  
  void initialize_dec_variables(const exprt &exp);
   
  protected:
  acdl_domaint &domain;
  bool phase;
};
#endif
