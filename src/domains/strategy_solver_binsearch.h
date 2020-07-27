/*******************************************************************\

Module: Simplified strategy iteration solver by binary search

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Simplified strategy iteration solver by binary search

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
    const local_SSAt &SSA,
    message_handlert &message_handler):
    strategy_solver_baset(_solver, SSA, message_handler),
    tpolyhedra_domain(_tpolyhedra_domain) {}

  virtual bool iterate(invariantt &inv);

protected:
  tpolyhedra_domaint &tpolyhedra_domain;
};

#endif
