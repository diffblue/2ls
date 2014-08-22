#ifndef CPROVER_RANKING_SOLVER_ENUMERATION_H 
#define CPROVER_RANKING_SOLVER_ENUMERATION_H 

#include "strategy_solver_base.h"
#include "linrank_domain.h"

class ranking_solver_enumerationt : public strategy_solver_baset 
{
 public:
  explicit ranking_solver_enumerationt(const constraintst &program,
    linrank_domaint &_linrank_domain,
    bv_pointerst &_solver, const namespacet &_ns) : 
  strategy_solver_baset(program, _solver, _ns),
  linrank_domain(_linrank_domain) {}

  virtual bool iterate(invariantt &inv);

 protected:
  linrank_domaint &linrank_domain;

};

#endif
