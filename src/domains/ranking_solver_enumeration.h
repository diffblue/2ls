#ifndef CPROVER_STRATEGY_SOLVER_ENUMERATION_H 
#define CPROVER_STRATEGY_SOLVER_ENUMERATION_H 

#include "strategy_solver_base.h"
#include "template_domain.h"

class strategy_solver_enumerationt : public strategy_solver_baset 
{
 public:
  explicit strategy_solver_enumerationt(const constraintst &program,
    replace_mapt &_renaming_map,
    template_domaint &_template_domain,
    bv_pointerst &_solver, const namespacet &_ns) : 
  strategy_solver_baset(program, _renaming_map, _solver, _ns),
  template_domain(_template_domain) {}

  virtual bool iterate(invariantt &inv);

 protected:
  template_domaint &template_domain;

};

#endif
