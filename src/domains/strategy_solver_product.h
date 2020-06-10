/*******************************************************************\

Module: Generic strategy solver for product combination domains

Author: Viktor Malik

\*******************************************************************/

/// \file
/// Generic strategy solver for product combination domains
/// The strategy solver infers invariants for multiple domains in parallel
/// (domains are side-by-side). Iteration of each domain is run in the context
/// of candidate invariants already inferred in all other domains.

#ifndef CPROVER_2LS_DOMAINS_STRATEGY_SOLVER_PRODUCT_H
#define CPROVER_2LS_DOMAINS_STRATEGY_SOLVER_PRODUCT_H

#include "strategy_solver_base.h"
#include "product_domain.h"
#include <memory>

typedef std::vector<std::unique_ptr<strategy_solver_baset>> solver_vect;

class strategy_solver_productt:public strategy_solver_baset
{
public:
  strategy_solver_productt(
    product_domaint &domain,
    incremental_solvert &solver,
    const namespacet &ns,
    solver_vect solvers):
    strategy_solver_baset(solver, ns), domain(domain),
    solvers(std::move(solvers)) {}

  bool iterate(invariantt &inv) override;

  void use_sympaths() override;
  void set_sympath(const symbolic_patht &sympath) override;
  void clear_symbolic_path() override;

protected:
  product_domaint &domain;
  // The solver contains a list of inner solvers
  solver_vect solvers;
};

#endif // CPROVER_2LS_DOMAINS_STRATEGY_SOLVER_PRODUCT_H
