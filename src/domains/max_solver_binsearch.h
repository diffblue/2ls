/*******************************************************************\

Module: Maximisation solver to compute under-approximations by binary search

Author: Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_2LS_DOMAINS_MAX_SOLVER_BINSEARCH_H
#define CPROVER_2LS_DOMAINS_MAX_SOLVER_BINSEARCH_H

#include "strategy_solver_base.h"
#include "tpolyhedra_domain.h"

class max_solver_binsearcht:public strategy_solver_baset
{
public:
  max_solver_binsearcht(
    tpolyhedra_domaint &_tpolyhedra_domain,
    incremental_solvert &_solver,
    const namespacet &_ns):
    strategy_solver_baset(_solver, _ns),
    tpolyhedra_domain(_tpolyhedra_domain)
  {
  }

  virtual bool iterate(invariantt &inv);

protected:
  tpolyhedra_domaint &tpolyhedra_domain;
};

#endif
