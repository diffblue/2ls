/*******************************************************************\

Module: Full strategy iteration solver by binary search

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Full strategy iteration solver by binary search

#ifndef CPROVER_2LS_DOMAINS_STRATEGY_SOLVER_BINSEARCH3_H
#define CPROVER_2LS_DOMAINS_STRATEGY_SOLVER_BINSEARCH3_H

#include <ssa/local_ssa.h>

#include "strategy_solver_base.h"
#include "tpolyhedra_domain.h"

class strategy_solver_binsearch3t:public strategy_solver_baset
{
 public:
  explicit strategy_solver_binsearch3t(
    tpolyhedra_domaint &_tpolyhedra_domain,
    incremental_solvert &_solver,
    const local_SSAt& _SSA,
    message_handlert &message_handler):
    strategy_solver_baset(_solver, _SSA, message_handler),
    tpolyhedra_domain(_tpolyhedra_domain),
    sum_bound_counter(0) {}

  virtual bool iterate(invariantt &inv);

 protected:
  tpolyhedra_domaint &tpolyhedra_domain;
  unsigned sum_bound_counter;
};

#endif // CPROVER_2LS_DOMAINS_STRATEGY_SOLVER_BINSEARCH3_H
