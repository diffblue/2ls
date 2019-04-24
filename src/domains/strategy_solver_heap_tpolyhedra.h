/*******************************************************************\

Module: Strategy solver for combination of shape and template
        polyhedra domains.

Author: Viktor Malik

\*******************************************************************/

/// \file
/// Strategy solver for combination of shape and template polyhedra domains.

#ifndef CPROVER_2LS_DOMAINS_STRATEGY_SOLVER_HEAP_TPOLYHEDRA_H
#define CPROVER_2LS_DOMAINS_STRATEGY_SOLVER_HEAP_TPOLYHEDRA_H


#include "strategy_solver_base.h"
#include "heap_tpolyhedra_domain.h"
#include "strategy_solver.h"
#include "strategy_solver_binsearch.h"

class strategy_solver_heap_tpolyhedrat:public strategy_solver_baset
{
public:
  strategy_solver_heap_tpolyhedrat(
    heap_tpolyhedra_domaint &_heap_tpolyhedra_domain,
    incremental_solvert &_solver,
    const local_SSAt &SSA,
    const exprt &precondition,
    message_handlert &message_handler,
    template_generator_baset &template_generator):
    strategy_solver_baset(_solver, SSA.ns),
    heap_tpolyhedra_domain(_heap_tpolyhedra_domain),
    heap_solver(
      heap_tpolyhedra_domain.heap_domain,
      _solver,
      SSA,
      precondition,
      message_handler,
      template_generator),
    tpolyhedra_solver(heap_tpolyhedra_domain.polyhedra_domain, _solver, SSA.ns)
  {
    tpolyhedra_solver.set_message_handler(message_handler);
  }

  virtual bool iterate(invariantt &_inv) override;

  virtual void set_message_handler(message_handlert &_message_handler) override;
  void clear_symbolic_path();

protected:
  heap_tpolyhedra_domaint &heap_tpolyhedra_domain;

  strategy_solvert heap_solver;
  strategy_solver_binsearcht tpolyhedra_solver;
};


#endif // CPROVER_2LS_DOMAINS_STRATEGY_SOLVER_HEAP_TPOLYHEDRA_H
