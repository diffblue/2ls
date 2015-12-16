/*******************************************************************\

Module: ACDL Decision Heuristics Interface

Author: Rajdeep Mukherjee, Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_ACDL_DECISION_HEURISTICS_H
#define CPROVER_ACDL_DECISION_HEURISTICS_H

#include <goto-programs/property_checker.h>

#include "acdl_domain.h"
#include "../ssa/local_ssa.h"

class acdl_decision_heuristicst : public messaget
{
public:
  
  //override this
  virtual acdl_domaint::meet_irreduciblet operator()(
    const local_SSAt &SSA,
    const acdl_domaint::valuet &value)
  {
    assert(false);
  }

protected:
  acdl_domaint &domain;

  explicit acdl_decision_heuristicst(
    acdl_domaint &_domain)
    : 
  domain(_domain)
  {
  }  

  ~acdl_decision_heuristicst() 
  {
  }
};

#endif
