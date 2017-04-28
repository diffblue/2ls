/**
 *  Viktor Malik, 3/30/17 (c).
 */
#ifndef INC_2LS_STRATEGY_SOLVER_HEAP_INTERVALT_H
#define INC_2LS_STRATEGY_SOLVER_HEAP_INTERVALT_H


#include "strategy_solver_base.h"
#include "heap_interval_domain.h"
#include "strategy_solver_heap.h"
#include "strategy_solver_binsearch.h"

class strategy_solver_heap_intervalt : public strategy_solver_baset
{
 public:
  strategy_solver_heap_intervalt(heap_interval_domaint &_heap_interval_domain,
                                 incremental_solvert &_solver, const local_SSAt &SSA,
                                 const exprt &precondition, message_handlert &message_handler,
                                 template_generator_baset &template_generator)
      : strategy_solver_baset(_solver, SSA.ns),
        heap_interval_domain(_heap_interval_domain),
        heap_solver(heap_interval_domain.heap_domain, _solver, SSA, precondition, message_handler,
                    template_generator),
        interval_solver(heap_interval_domain.interval_domain, _solver, SSA.ns) {}

  virtual bool iterate(invariantt &_inv) override;

  virtual void set_message_handler(message_handlert &_message_handler) override;

 protected:
  heap_interval_domaint &heap_interval_domain;

  strategy_solver_heapt heap_solver;
  strategy_solver_binsearcht interval_solver;
};


#endif //INC_2LS_STRATEGY_SOLVER_HEAP_INTERVALT_H
