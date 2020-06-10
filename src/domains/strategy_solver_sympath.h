/*******************************************************************\

Module: Generic strategy solver for domain with symbolic paths

Author: Viktor Malik

\*******************************************************************/

/// \file
/// Generic strategy solver for domain with symbolic paths

#ifndef CPROVER_2LS_DOMAINS_STRATEGY_SOLVER_SYMPATH_H
#define CPROVER_2LS_DOMAINS_STRATEGY_SOLVER_SYMPATH_H


#include "strategy_solver_base.h"
#include "sympath_domain.h"

class strategy_solver_sympatht:public strategy_solver_baset
{
public:
  strategy_solver_sympatht(
    sympath_domaint &_domain,
    incremental_solvert &_solver,
    const local_SSAt &SSA,
    std::unique_ptr<strategy_solver_baset> _inner_solver):
    strategy_solver_baset(_solver, SSA.ns),
    domain(_domain),
    inner_solver(std::move(_inner_solver))
  {
    build_loop_conds_map(SSA);
    inner_solver->use_sympaths();
  }

  bool iterate(invariantt &inv) override;

  void clear_symbolic_path() override;

protected:
  sympath_domaint &domain;

  // Strategy solver for the inner domain
  std::unique_ptr<strategy_solver_baset> inner_solver;

  std::vector<symbolic_patht> visited_paths;
  bool new_path=true;

  // Mapping for each loop:
  // g#ls    ->    (g#lh   &&   g#le)
  // ^ loop select  ^ loop head ^ loop end
  // This is used to check feasibility of symbolic paths
  std::map<exprt, const exprt> loop_conds_map;
  void build_loop_conds_map(const local_SSAt &SSA);

  bool is_current_path_feasible(
    sympath_domaint::sympath_valuet &value);
};

#endif // CPROVER_2LS_DOMAINS_STRATEGY_SOLVER_SYMPATH_H
