/*******************************************************************\

Module: ACDL Decision Heuristics (Branch on Condition Variables)

Author: Rajdeep Mukherjee, Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_ACDL_DECISION_HEURISTICS_COND_H
#define CPROVER_ACDL_DECISION_HEURISTICS_COND_H

#include "acdl_decision_heuristics.h"

class acdl_decision_heuristics_condt : public acdl_decision_heuristicst
{
public:
  explicit acdl_decision_heuristics_condt(
    acdl_domaint &_domain)
    : 
  acdl_decision_heuristicst(_domain)
  {
  }

  
  typedef std::list<exprt> conds;
  virtual acdl_domaint::meet_irreduciblet operator()(
    const local_SSAt &SSA,
    const acdl_domaint::valuet &value);

};

#endif
