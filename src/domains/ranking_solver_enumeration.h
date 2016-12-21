#ifndef CPROVER_2LS_DOMAINS_RANKING_SOLVER_ENUMERATION_H
#define CPROVER_2LS_DOMAINS_RANKING_SOLVER_ENUMERATION_H

#include <solvers/sat/satcheck.h>
#include <solvers/flattening/bv_pointers.h>

#include "strategy_solver_base.h"
#include "../domains/incremental_solver.h"
#include "linrank_domain.h"

class ranking_solver_enumerationt : public strategy_solver_baset
{
 public:
  explicit ranking_solver_enumerationt(
    linrank_domaint &_linrank_domain,
    incremental_solvert &_solver,
    const namespacet &_ns,
    unsigned _max_inner_iterations
    ) :
    strategy_solver_baset(_solver, _ns),
    linrank_domain(_linrank_domain),
    max_inner_iterations(_max_inner_iterations),
    inner_solver(_ns),
    number_inner_iterations(0)
 {
   solver_instances++;
 }

  virtual bool iterate(invariantt &inv);

 protected:
  linrank_domaint &linrank_domain;

  // the "inner" solver
  const unsigned max_inner_iterations;
  incremental_solvert inner_solver;
  unsigned number_inner_iterations;
};

#endif
