/*******************************************************************\

Module: ACDL Decision Heuristics (random)

Author: Rajdeep Mukherjee, Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_2LS_ACDL_ACDL_DECISION_HEURISTICS_RAND_H
#define CPROVER_2LS_ACDL_ACDL_DECISION_HEURISTICS_RAND_H

#include "acdl_decision_heuristics_base.h"

class acdl_decision_heuristics_randt : public acdl_decision_heuristics_baset
{
public:
  explicit acdl_decision_heuristics_randt(
    acdl_domaint &_domain)
    :
  acdl_decision_heuristics_baset(_domain)
  {
  }

  virtual acdl_domaint::meet_irreduciblet operator()(
    const local_SSAt &SSA,
    const acdl_domaint::valuet &value);

protected:

  typedef std::pair<exprt, acdl_domaint::statementt> dec_pair;
  typedef std::list<dec_pair> conds;
};

#endif
