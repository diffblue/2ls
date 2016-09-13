/**
 * Strategy solver for heap verification.
 *  Viktor Malik, 12.8.2016 (c).
 */
#ifndef CPROVER_STRATEGY_SOLVER_HEAP_H
#define CPROVER_STRATEGY_SOLVER_HEAP_H

#include "strategy_solver_base.h"
#include "heap_domain.h"

class strategy_solver_heapt : public strategy_solver_baset
{
 public:
  explicit strategy_solver_heapt(heap_domaint &_heap_domain, incremental_solvert &_solver,
                                 const namespacet &_ns)
      : strategy_solver_baset(_solver, _ns), heap_domain(_heap_domain)
  {
  }

  virtual bool iterate(invariantt &_inv) override;

 protected:
  heap_domaint &heap_domain;

  int find_member_row(const exprt &obj, const irep_idt &member, int actual_loc);
};


#endif //CPROVER_STRATEGY_SOLVER_HEAP_H
