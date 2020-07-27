/*******************************************************************\

Module: SSA Analyzer

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// SSA Analyzer

#ifndef CPROVER_2LS_DOMAINS_SSA_ANALYZER_H
#define CPROVER_2LS_DOMAINS_SSA_ANALYZER_H

#include <util/replace_expr.h>

#include <solver/summary.h>
#include <ssa/local_ssa.h>

#include "strategy_solver_base.h"
#include "template_generator_base.h"

class ssa_analyzert:public messaget
{
public:
  typedef strategy_solver_baset::constraintst constraintst;
  typedef strategy_solver_baset::var_listt var_listt;

  void operator()(
    incremental_solvert &solver,
    local_SSAt &SSA,
    const exprt &precondition,
    template_generator_baset &template_generator);

  void get_result(exprt &result, const var_sett &vars);

  inline unsigned get_number_of_solver_instances() { return solver_instances; }
  inline unsigned get_number_of_solver_calls() { return solver_calls; }

protected:
  domaint *domain; // template generator is responsible for the domain object
  std::unique_ptr<domaint::valuet> result;

  // statistics
  unsigned solver_instances;
  unsigned solver_calls;
};

#endif

