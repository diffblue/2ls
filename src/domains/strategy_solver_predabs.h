#ifndef CPROVER_STRATEGY_SOLVER_PREDABS_H
#define CPROVER_STRATEGY_SOLVER_PREDABS_H 

#include "strategy_solver_base.h"
#include "predabs_domain.h"

class strategy_solver_predabst : public strategy_solver_baset
{
 public:
  explicit strategy_solver_predabst(
    const constraintst &program,
    predabs_domaint &_predabs_domain,
    bv_pointerst &_solver, 
    const namespacet &_ns) : 
  strategy_solver_baset(program, _solver, _ns),
    predabs_domain(_predabs_domain)
  {
  }

  virtual bool iterate(invariantt &inv);

 protected:
  predabs_domaint &predabs_domain;
};

#endif
