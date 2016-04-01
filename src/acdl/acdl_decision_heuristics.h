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
  
  explicit acdl_decision_heuristicst(
    acdl_domaint &_domain)
    : 
  domain(_domain)
  {
  }  

  virtual ~acdl_decision_heuristicst() 
  {
  }
  
  //override this
  acdl_domaint::meet_irreduciblet operator()(
    const local_SSAt &SSA,
    const acdl_domaint::valuet &value);
  /*{
    assert(false);
  }*/
  acdl_domaint::statementt dec_statement;
  std::set<exprt> decision_variables;
  /******* decision heuristics *******/
  enum dec_heurt { RANGE, RANGE_REL, BERKMIN, RAND };
  dec_heurt dec_heur;

protected:
  acdl_domaint &domain;

  
  typedef std::pair<exprt, acdl_domaint::statementt> dec_pair;
  typedef std::list<dec_pair> conds;

  acdl_domaint::meet_irreduciblet dec_heur_largest_range(const local_SSAt &SSA, const acdl_domaint::valuet &value, bool phase);
  acdl_domaint::meet_irreduciblet dec_heur_berkmin(const local_SSAt &SSA, const acdl_domaint::valuet &value);
  acdl_domaint::meet_irreduciblet dec_heur_rand(const local_SSAt &SSA, const acdl_domaint::valuet &value);

protected:
  bool phase;

};

#endif
