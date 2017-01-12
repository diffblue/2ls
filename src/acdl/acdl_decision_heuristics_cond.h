/*******************************************************************\

Module: ACDL Decision Heuristics (Branch on Condition Variables)

Author: Rajdeep Mukherjee, Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_2LS_ACDL_ACDL_DECISION_HEURISTICS_COND_H
#define CPROVER_2LS_ACDL_ACDL_DECISION_HEURISTICS_COND_H

#include "acdl_decision_heuristics.h"

class acdl_decision_heuristics_condt : public acdl_decision_heuristics_baset
{
public:
  explicit acdl_decision_heuristics_condt(
    acdl_domaint &_domain)
    :
  acdl_decision_heuristics_baset(_domain)
  {
  }

  typedef std::pair<exprt, acdl_domaint::statementt> dec_pair;
  typedef std::list<dec_pair> conds;

  virtual acdl_domaint::meet_irreduciblet operator()(
    const local_SSAt &SSA,
    const acdl_domaint::valuet &value);
};

#endif
