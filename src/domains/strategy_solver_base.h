#ifndef CPROVER_STRATEGY_SOLVER_BASE_H
#define CPROVER_STRATEGY_SOLVER_BASE_H 

#include <map>
#include <iostream>

#include <solvers/flattening/bv_pointers.h>

#include "domain.h"
#include "util.h"
#include "../domains/incremental_solver.h"


//#define DEBUG_FORMULA

class strategy_solver_baset : public messaget
{

 public:
  typedef std::list<exprt> constraintst;
  typedef std::vector<symbol_exprt> var_listt;
  typedef domaint::valuet invariantt;

  explicit strategy_solver_baset(
    incremental_solvert &_solver, 
    const namespacet &_ns) :
    solver(_solver), 
    ns(_ns),
    solver_calls(0)
  {}

  virtual bool iterate(invariantt &inv) { assert(false); }

  unsigned get_number_of_solver_calls() { return solver_calls; }
  unsigned get_number_of_solver_instances() { return solver_instances; }

 protected: 
  incremental_solvert &solver;

  const namespacet &ns;

  //handles on values to retrieve from model
  bvt strategy_cond_literals;
  exprt::operandst strategy_value_exprs;

  //statistics
  unsigned solver_instances;
  unsigned solver_calls;
};

#endif
