/*******************************************************************\

Module: SSA Analyzer

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// SSA Analyzer

#ifdef DEBUG
#include <iostream>
#endif

#include <solvers/sat/satcheck.h>
#include <solvers/flattening/bv_pointers.h>
#include <util/find_symbols.h>
#include <util/arith_tools.h>
#include <util/simplify_expr.h>
#include <util/mp_arith.h>
#include <util/options.h>

#include "strategy_solver_base.h"
#include "strategy_solver_binsearch.h"
#include "strategy_solver_binsearch2.h"
#include "strategy_solver_binsearch3.h"
#include "linrank_domain.h"
#include "equality_domain.h"
#include "lexlinrank_domain.h"
#include "predabs_domain.h"
#include "template_generator_ranking.h"
#include "ssa_analyzer.h"
#include "strategy_solver_sympath.h"
#include "strategy_solver_simple.h"
#include "heap_domain.h"
#include "strategy_solver_product.h"

// NOLINTNEXTLINE(*)
#define SIMPLE_SOLVER(domain_ptr, domain_type) strategy_solver_simplet(\
  *dynamic_cast<domain_type *>(domain_ptr), \
  solver, \
  SSA, \
  get_message_handler())
#define BINSEARCH_SOLVER strategy_solver_binsearcht(\
  *dynamic_cast<tpolyhedra_domaint *>(simple_domains[next_domain++]), \
  solver, \
  SSA, \
  get_message_handler())
#if 0
// NOLINTNEXTLINE(*)
#define BINSEARCH_SOLVER strategy_solver_binsearch2t(\
  *static_cast<tpolyhedra_domaint *>(domain), solver, SSA.ns)
// NOLINTNEXTLINE(*)
#define BINSEARCH_SOLVER strategy_solver_binsearch3t(\
  *static_cast<tpolyhedra_domaint *>(domain), solver, SSA, SSA.ns)
#endif

void ssa_analyzert::operator()(
  incremental_solvert &solver,
  local_SSAt &SSA,
  const exprt &precondition,
  template_generator_baset &template_generator)
{
  if(SSA.goto_function.body.instructions.empty())
    return;

  solver << SSA;
  SSA.mark_nodes();

  solver.new_context();
  solver << SSA.get_enabling_exprs();

  // add precondition (or conjunction of asssertion in backward analysis)
  solver << precondition;

  domain=template_generator.domain();

  // Get a strategy solver and a new abstract value (invariant)
  auto s_solver=domain->new_strategy_solver(solver, SSA, get_message_handler());
  result=domain->new_value();

  // initialize inv
  domain->initialize_value(*result);

  // iterate
  while(s_solver->iterate(*result)) {}

  solver.pop_context();

  // statistics
  solver_instances+=s_solver->get_number_of_solver_instances();
  solver_calls+=s_solver->get_number_of_solver_calls();
  solver_instances+=s_solver->get_number_of_solver_instances();
}

void ssa_analyzert::get_result(exprt &_result, const var_sett &vars)
{
  domain->project_on_vars(*result, vars, _result);
}
