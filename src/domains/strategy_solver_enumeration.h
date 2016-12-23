/*******************************************************************\

Module: Synthesis by enumeration of counterexamples

Author: Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_2LS_DOMAINS_STRATEGY_SOLVER_ENUMERATION_H
#define CPROVER_2LS_DOMAINS_STRATEGY_SOLVER_ENUMERATION_H

#include "strategy_solver_base.h"
#include "tpolyhedra_domain.h"

class strategy_solver_enumerationt:public strategy_solver_baset
{
public:
  strategy_solver_enumerationt(
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
