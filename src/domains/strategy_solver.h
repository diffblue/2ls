/*******************************************************************\

Module: Generic strategy solver

Author: Matej Marusak

\*******************************************************************/
/// \file
/// Generic strategy solver

#ifndef CPROVER_2LS_DOMAINS_STRATEGY_SOLVER_H
#define CPROVER_2LS_DOMAINS_STRATEGY_SOLVER_H

#include <ssa/local_ssa.h>
#include "strategy_solver_base.h"
#include "domain.h"
#include "template_generator_base.h"

class strategy_solvert:public strategy_solver_baset
{
public:
  strategy_solvert(
    domaint &_domain,
    incremental_solvert &_solver,
    const local_SSAt &SSA,
    const exprt &precondition,
    message_handlert &message_handler,
    template_generator_baset &template_generator):
    strategy_solver_baset(_solver, SSA.ns), domain(_domain),
    loop_guards(SSA.loop_guards)
  {
    set_message_handler(message_handler);
    solver << domain.initialize_solver(SSA, precondition, template_generator);
  }

  virtual bool iterate(invariantt &_inv) override;

protected:
  domaint &domain;
  std::set<std::pair<symbol_exprt, symbol_exprt>> loop_guards;
};

#endif // CPROVER_2LS_DOMAINS_STRATEGY_SOLVER_H
