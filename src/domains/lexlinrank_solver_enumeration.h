/*******************************************************************\

Module: Abstract domain base class

Author: Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_2LS_DOMAINS_LEXLINRANK_SOLVER_ENUMERATION_H
#define CPROVER_2LS_DOMAINS_LEXLINRANK_SOLVER_ENUMERATION_H

#include "strategy_solver_base.h"
#include "../domains/incremental_solver.h"
#include "lexlinrank_domain.h"
#include <solvers/sat/satcheck.h>
#include <solvers/flattening/bv_pointers.h>


class lexlinrank_solver_enumerationt:public strategy_solver_baset
{
 public:
  explicit lexlinrank_solver_enumerationt(
    lexlinrank_domaint &_lexlinrank_domain,
    incremental_solvert &_solver,
    const namespacet &_ns,
    unsigned _max_elements, // lexicographic components
    unsigned _max_inner_iterations):
    strategy_solver_baset(_solver, _ns),
    lexlinrank_domain(_lexlinrank_domain),
    max_elements(_max_elements),
    max_inner_iterations(_max_inner_iterations),
    number_inner_iterations(0)
  {
    inner_solver=incremental_solvert::allocate(_ns);
    solver_instances++;
  }

  virtual bool iterate(invariantt &inv);

 protected:
  lexlinrank_domaint &lexlinrank_domain;
  const unsigned max_elements; // lexicographic components

  // the "inner" solver
  const unsigned max_inner_iterations;
  incremental_solvert *inner_solver;
  unsigned number_inner_iterations;
};

#endif
