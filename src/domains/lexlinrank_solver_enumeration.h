#ifndef CPROVER_LEXLINRANK_SOLVER_ENUMERATION_H 
#define CPROVER_LEXLINRANK_SOLVER_ENUMERATION_H 

#include "strategy_solver_base.h"
#include "../domains/incremental_solver.h"
#include "lexlinrank_domain.h"
#include <solvers/sat/satcheck.h>
#include <solvers/flattening/bv_pointers.h>


class lexlinrank_solver_enumerationt : public strategy_solver_baset 
{
 public:
  explicit lexlinrank_solver_enumerationt(
    lexlinrank_domaint &_lexlinrank_domain,
    incremental_solvert &_solver, 
    const namespacet &_ns) : 
  strategy_solver_baset(_solver, _ns),
    lexlinrank_domain(_lexlinrank_domain), 
    number_refinements(0)
  {
    inner_solver = incremental_solvert::allocate(_ns);
    solver_instances++;
  }

  virtual bool iterate(invariantt &inv);

 protected:
  lexlinrank_domaint &lexlinrank_domain;

  // the "inner" solver
  incremental_solvert *inner_solver;
  unsigned number_refinements; 

};

#endif
