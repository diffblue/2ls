/*******************************************************************\

Module: ACDL Decision Heuristics (Assumption-Conditional-Read-only-rest)

Author: Rajdeep Mukherjee, Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_2LS_ACDL_ACDL_DECISION_HEURISTICS_EQUALITY_H
#define CPROVER_2LS_ACDL_ACDL_DECISION_HEURISTICS_EQUALITY_H

#include "acdl_decision_heuristics_base.h"

class acdl_decision_heuristics_equalityt : public acdl_decision_heuristics_baset
{
public:
  explicit acdl_decision_heuristics_equalityt(
    acdl_domaint &_domain)
    :
  acdl_decision_heuristics_baset(_domain)
  {
  }

  virtual acdl_domaint::meet_irreduciblet operator()(
    const local_SSAt &SSA,
    const acdl_domaint::valuet &value);

protected:
  std::vector<exprt> equality_decision_container;
  
};

#endif
