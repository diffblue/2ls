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
#define BINSEARCH_SOLVER strategy_solver_binsearcht(\
  *static_cast<tpolyhedra_domaint *>(domain), solver, SSA.ns)
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

  // get strategy solver from options
  strategy_solver_baset *s_solver;
  if(template_generator.options.get_bool_option("compute-ranking-functions"))
  {
    if(template_generator.options.get_bool_option(
      "monolithic-ranking-function"))
    {
      s_solver=new strategy_solver_simplet(
        *static_cast<linrank_domaint *>(domain),
        solver,
        SSA,
        precondition,
        get_message_handler(),
        template_generator);
      result=new linrank_domaint::templ_valuet();
    }
    else
    {
      s_solver=new strategy_solver_simplet(
        *static_cast<lexlinrank_domaint *>(domain),
        solver,
        SSA,
        precondition,
        get_message_handler(),
        template_generator);
      result=new lexlinrank_domaint::templ_valuet();
    }
  }
  else if(template_generator.options.get_bool_option("equalities"))
  {
    s_solver=new strategy_solver_simplet(
      *static_cast<equality_domaint *>(domain),
      solver,
      SSA,
      precondition,
      get_message_handler(),
      template_generator);
    result=new equality_domaint::equ_valuet();
  }
  else if(template_generator.options.get_bool_option("heap"))
  {
    s_solver=new strategy_solver_simplet(
      *static_cast<heap_domaint *>(domain),
      solver,
      SSA,
      precondition,
      get_message_handler(),
      template_generator);
    result=new heap_domaint::heap_valuet();
  }
  else if(template_generator.options.get_bool_option("heap-interval")
          || template_generator.options.get_bool_option("heap-zones"))
  {
    // Heap-tpolyhedra domain is represented as a product domain. If the sympath
    // option is on, it is stored inside heap_tpolyhedra_sympath_domaint.
    auto *product_domain=
      dynamic_cast<product_domaint *>(
        template_generator.options.get_bool_option("sympath")
        ? dynamic_cast<sympath_domaint *>(domain)
          ->inner_domain
        : domain);

    // Initialize heap solver (heap domain is the first one in the product
    // domain) and value.
    auto heap_solver=new strategy_solver_simplet(
      *dynamic_cast<heap_domaint *>(product_domain->domains.at(0)),
      solver,
      SSA,
      precondition,
      get_message_handler(),
      template_generator);
    auto heap_value=new heap_domaint::heap_valuet();
    // Initialize tpolyhedra solver (tpolyhedra domain is the second one in the
    // product domain) and value.
    auto tpolyhedra_solver=new strategy_solver_binsearcht(
      *dynamic_cast<tpolyhedra_domaint *>(product_domain->domains.at(1)),
      solver,
      SSA.ns);
    auto tpolyhedra_value=new tpolyhedra_domaint::templ_valuet();

    // Initialize product solver and value
    s_solver=new strategy_solver_productt(
      *product_domain,
      solver,
      SSA.ns,
      {heap_solver, tpolyhedra_solver});
    result=new product_domaint::valuet({heap_value, tpolyhedra_value});

    if(template_generator.options.get_bool_option("sympath"))
    {
      // Initialize sympath solver and value
      s_solver=new strategy_solver_sympatht(
        *dynamic_cast<sympath_domaint *>(domain), solver, SSA, s_solver);
      result=new sympath_domaint::sympath_valuet(result);
    }
  }
  else
  {
    if(template_generator.options.get_bool_option("enum-solver"))
    {
      s_solver=new strategy_solver_simplet(
        *static_cast<tpolyhedra_domaint *>(domain),
        solver,
        SSA,
        precondition,
        get_message_handler(),
        template_generator);
      result=new tpolyhedra_domaint::templ_valuet();
    }
    else if(template_generator.options.get_bool_option("predabs-solver"))
    {
      s_solver=new strategy_solver_simplet(
        *static_cast<predabs_domaint *>(domain),
        solver,
        SSA,
        precondition,
        get_message_handler(),
        template_generator);
      result=new predabs_domaint::templ_valuet();
    }
    else if(template_generator.options.get_bool_option("binsearch-solver"))
    {
      result=new tpolyhedra_domaint::templ_valuet();
      s_solver=new BINSEARCH_SOLVER;
    }
    else
      assert(false);
  }

  s_solver->set_message_handler(get_message_handler());

  // initialize inv
  domain->initialize_value(*result);

  // iterate
  while(s_solver->iterate(*result)) {}

  solver.pop_context();

  // statistics
  solver_instances+=s_solver->get_number_of_solver_instances();
  solver_calls+=s_solver->get_number_of_solver_calls();
  solver_instances+=s_solver->get_number_of_solver_instances();

  delete s_solver;
}

void ssa_analyzert::get_result(exprt &_result, const var_sett &vars)
{
  domain->project_on_vars(*result, vars, _result);
}
