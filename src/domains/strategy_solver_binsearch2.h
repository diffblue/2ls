#ifndef CPROVER_STRATEGY_SOLVER_BINSEARCH2_H 
#define CPROVER_STRATEGY_SOLVER_BINSEARCH2_H 
 
#include "strategy_solver_base.h"
#include "tpolyhedra_domain.h"

class strategy_solver_binsearch2t : public strategy_solver_baset 
{
 public:
  explicit strategy_solver_binsearch2t(const constraintst &program,
    tpolyhedra_domaint &_tpolyhedra_domain,
    bv_pointerst &_solver, const namespacet &_ns) : 
    strategy_solver_baset(program, _solver, _ns),
    tpolyhedra_domain(_tpolyhedra_domain),
    sum_bound_counter(0) {}

  virtual bool iterate(invariantt &inv);

 protected:
  tpolyhedra_domaint &tpolyhedra_domain;
  unsigned sum_bound_counter;

};

#endif
