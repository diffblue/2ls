/*******************************************************************\

Module: Strategy iteration solver by binary search
        with optimisation of the parameter sum

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Strategy iteration solver by binary search with optimisation of the
///   parameter sum

#ifndef CPROVER_2LS_DOMAINS_STRATEGY_SOLVER_BINSEARCH2_H
#define CPROVER_2LS_DOMAINS_STRATEGY_SOLVER_BINSEARCH2_H

#include "strategy_solver_base.h"
#include "tpolyhedra_domain.h"

class strategy_solver_binsearch2t:public strategy_solver_baset
{
 public:
  strategy_solver_binsearch2t(
    tpolyhedra_domaint &_tpolyhedra_domain,
    incremental_solvert &_solver,
    const local_SSAt &SSA,
    message_handlert &message_handler):
    strategy_solver_baset(_solver, SSA, message_handler),
    tpolyhedra_domain(_tpolyhedra_domain),
    sum_bound_counter(0) {}

  virtual bool iterate(invariantt &inv);

 protected:
  tpolyhedra_domaint &tpolyhedra_domain;
  unsigned sum_bound_counter;
};


#endif
