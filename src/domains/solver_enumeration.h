#ifndef CPROVER_2LS_DOMAINS_SOLVER_ENUMERATION_H
#define CPROVER_2LS_DOMAINS_SOLVER_ENUMERATION_H

#include "strategy_solver_base.h"
#include "tpolyhedra_domain.h"

class solver_enumerationt : public strategy_solver_baset
{
 public:
  explicit solver_enumerationt(const constraintst &program,
    tpolyhedra_domaint &_tpolyhedra_domain,
    bv_pointerst &_solver, const namespacet &_ns) :
  strategy_solver_baset(program, _solver, _ns),
  tpolyhedra_domain(_tpolyhedra_domain) {}

  virtual bool iterate(invariantt &inv);

 protected:
  tpolyhedra_domaint &tpolyhedra_domain;

};

#endif
