/*******************************************************************\

Module: Strategy iteration solver base class

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Strategy iteration solver base class

#ifndef CPROVER_2LS_DOMAINS_STRATEGY_SOLVER_BASE_H
#define CPROVER_2LS_DOMAINS_STRATEGY_SOLVER_BASE_H

#include "domain.h"
#include "incremental_solver.h"
#include "util.h"
#include "symbolic_path.h"

class strategy_solver_baset:public messaget
{
 public:
  typedef std::list<exprt> constraintst;
  typedef std::vector<symbol_exprt> var_listt;
  typedef domaint::valuet invariantt;

  explicit strategy_solver_baset(
    incremental_solvert &_solver,
    const namespacet &_ns):
    solver(_solver),
    ns(_ns),
    solver_instances(0),
    solver_calls(0)
  {}

  virtual bool iterate(invariantt &inv) { assert(false); }

  inline unsigned get_number_of_solver_calls() { return solver_calls; }
  inline unsigned get_number_of_solver_instances() { return solver_instances; }

  symbolic_patht symbolic_path;

 protected:
  incremental_solvert &solver;
  const namespacet &ns;

  // handles on values to retrieve from model
  bvt strategy_cond_literals;
  exprt::operandst strategy_value_exprs;

  // statistics for additional solvers
  unsigned solver_instances;
  unsigned solver_calls;

  void find_symbolic_path(
    std::set<std::pair<symbol_exprt, symbol_exprt>> &loop_guards,
    const exprt &current_guard=nil_exprt());
};

#endif
