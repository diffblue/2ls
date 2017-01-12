/*******************************************************************\

Module: ACDL Decision Heuristics (range)

Author: Rajdeep Mukherjee, Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_2LS_ACDL_ACDL_DECISION_HEURISTICS_LARGEST_RANGE_H
#define CPROVER_2LS_ACDL_ACDL_DECISION_HEURISTICS_LARGEST_RANGE_H

#include "acdl_decision_heuristics_base.h"

class acdl_decision_heuristics_ranget : public acdl_decision_heuristics_baset
{
public:
  explicit acdl_decision_heuristics_ranget(
    acdl_domaint &_domain)
    :
  acdl_decision_heuristics_baset(_domain)
  {
  }

  virtual acdl_domaint::meet_irreduciblet operator()(
    const local_SSAt &SSA,
    const acdl_domaint::valuet &value);
  void get_scores(const acdl_domaint::valuet &value,
                  std::vector<double>& scores, bool relative);
  double get_ratio(std::pair<mp_integer, mp_integer> i1,
                   std::pair<mp_integer, mp_integer> i2);

protected:
};

#endif
