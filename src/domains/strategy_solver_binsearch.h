#ifndef CPROVER_STRATEGY_SOLVER_BINSEARCH_H 
#define CPROVER_STRATEGY_SOLVER_BINSEARCH_H 

#include "strategy_solver_base.h"
#include "tpolyhedra_domain.h"

class strategy_solver_binsearcht : public strategy_solver_baset 
{
 public:
  explicit strategy_solver_binsearcht(const constraintst &program,
    tpolyhedra_domaint &_tpolyhedra_domain,
    bv_pointerst &_solver, const namespacet &_ns) : 
  strategy_solver_baset(program, _solver, _ns),
  tpolyhedra_domain(_tpolyhedra_domain) {}

  virtual bool iterate(invariantt &inv);

 protected:
  tpolyhedra_domaint &tpolyhedra_domain;

};

#endif
