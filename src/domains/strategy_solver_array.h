/*******************************************************************\

Module: Strategy solver for the array abstract domain

Author: Viktor Malik <viktor.malik@gmail.com>

\*******************************************************************/
/// \file
/// Strategy solver for the array abstract domain
/// The strategy solver infers invariants for array elements (using symbolic
/// element variables) in the inner domain.

#ifndef CPROVER_2LS_DOMAINS_STRATEGY_SOLVER_ARRAY_H
#define CPROVER_2LS_DOMAINS_STRATEGY_SOLVER_ARRAY_H

#include "array_domain.h"
#include "strategy_solver_base.h"

class strategy_solver_arrayt : public strategy_solver_baset
{
public:
  strategy_solver_arrayt(array_domaint &domain,
                         std::unique_ptr<strategy_solver_baset> inner_solver,
                         incremental_solvert &solver,
                         const local_SSAt &SSA,
                         message_handlert &message_handler)
    : strategy_solver_baset(solver, SSA, message_handler),
      domain(domain),
      inner_solver(std::move(inner_solver))
  {
  }

  bool iterate(invariantt &inv) override;
  void use_sympaths() override;
  void set_sympath(const symbolic_patht &sympath) override;
  void clear_symbolic_path() override;

protected:
  array_domaint &domain;
  std::unique_ptr<strategy_solver_baset> inner_solver;
};

#endif // CPROVER_2LS_DOMAINS_STRATEGY_SOLVER_ARRAY_H
