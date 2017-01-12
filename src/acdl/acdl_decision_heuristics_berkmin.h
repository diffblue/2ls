/*******************************************************************\

Module: ACDL Decision Heuristics (ordered)

Author: Rajdeep Mukherjee, Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_ACDL_DECISION_HEURISTICS_BERKMIN_H
#define CPROVER_ACDL_DECISION_HEURISTICS_BERKMIN_H

#include "acdl_decision_heuristics_base.h"
#include "acdl_analyze_conflict_base.h"

class acdl_decision_heuristics_berkmint : public acdl_decision_heuristics_baset
{
public:
  explicit acdl_decision_heuristics_berkmint(
    acdl_domaint &_domain,
    acdl_analyze_conflict_baset &_conflict_analysis)
    : 
  acdl_decision_heuristics_baset(_domain),
  conflict_analysis(_conflict_analysis)
  {
  }
  
  virtual acdl_domaint::meet_irreduciblet operator()(
  const local_SSAt &SSA,
  const acdl_domaint::valuet &value);
  
protected:  
  acdl_analyze_conflict_baset &conflict_analysis;
  acdl_domaint::meet_irreduciblet random_dec_heuristics(const local_SSAt &SSA, const acdl_domaint::valuet &value);
};

#endif
