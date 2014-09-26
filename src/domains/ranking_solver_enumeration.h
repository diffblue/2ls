#ifndef CPROVER_RANKING_SOLVER_ENUMERATION_H 
#define CPROVER_RANKING_SOLVER_ENUMERATION_H 

#include <solvers/sat/satcheck.h>
#include <solvers/flattening/bv_pointers.h>

#include "strategy_solver_base.h"
#include "linrank_domain.h"

class ranking_solver_enumerationt : public strategy_solver_baset 
{
 public:
  explicit ranking_solver_enumerationt(const constraintst &program,
    linrank_domaint &_linrank_domain,
    bv_pointerst &_solver, const namespacet &_ns) : 
    strategy_solver_baset(program, _solver, _ns),
    linrank_domain(_linrank_domain),
    inner_satcheck(),
    inner_solver(_ns, inner_satcheck), 
    number_inner_iterations(0)
 {}

  virtual bool iterate(invariantt &inv);

 protected:
  linrank_domaint &linrank_domain;

  // the "inner" solver
  satcheck_minisat_no_simplifiert inner_satcheck;
  bv_pointerst inner_solver;
  int number_inner_iterations;


};

#endif
