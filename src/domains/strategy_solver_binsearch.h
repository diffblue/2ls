/*******************************************************************\

Module: Simplified strategy iteration solver by binary search

Author: Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_2LS_DOMAINS_STRATEGY_SOLVER_BINSEARCH_H
#define CPROVER_2LS_DOMAINS_STRATEGY_SOLVER_BINSEARCH_H

#include "strategy_solver_base.h"
#include "tpolyhedra_domain.h"

class strategy_solver_binsearcht:public strategy_solver_baset
{
public:
  strategy_solver_binsearcht(
    tpolyhedra_domaint &_tpolyhedra_domain,
    incremental_solvert &_solver,
    const namespacet &_ns):
    strategy_solver_baset(_solver, _ns),
    tpolyhedra_domain(_tpolyhedra_domain)
  {
  }

  virtual bool iterate(invariantt &inv);
  virtual bool iterate_for_ins(invariantt &inv);
protected:
  tpolyhedra_domaint &tpolyhedra_domain;
};

#endif
