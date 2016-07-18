/*******************************************************************\

Module: ACDL Decision Heuristics (ordered)

Author: Rajdeep Mukherjee, Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_ACDL_DECISION_HEURISTICS_ORDERED_H
#define CPROVER_ACDL_DECISION_HEURISTICS_ORDERED_H

#include "acdl_decision_heuristics_base.h"

class acdl_decision_heuristics_orderedt : public acdl_decision_heuristics_baset
{
public:
  explicit acdl_decision_heuristics_orderedt(
    acdl_domaint &_domain)
    : 
  acdl_decision_heuristics_baset(_domain)
  {
  }
  
  virtual acdl_domaint::meet_irreduciblet operator()(
  const local_SSAt &SSA,
  const acdl_domaint::valuet &value);
  
protected:  
};

#endif
