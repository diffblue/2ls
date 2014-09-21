#ifndef CPROVER_LEXLINRANK_SOLVER_ENUMERATION_H 
#define CPROVER_LEXLINRANK_SOLVER_ENUMERATION_H 

#include "strategy_solver_base.h"
#include "lexlinrank_domain.h"

class lexlinrank_solver_enumerationt : public strategy_solver_baset 
{
 public:
  explicit lexlinrank_solver_enumerationt(const constraintst &program,
    lexlinrank_domaint &_linrank_domain,
    bv_pointerst &_solver, const namespacet &_ns) : 
  strategy_solver_baset(program, _solver, _ns),
  lexlinrank_domain(_linrank_domain) {}

  virtual bool iterate(invariantt &inv);

 protected:
  lexlinrank_domaint &lexlinrank_domain;

};

#endif
