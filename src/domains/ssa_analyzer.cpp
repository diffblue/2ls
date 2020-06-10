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
  precondition, \
  get_message_handler(), \
  template_generator)
#define BINSEARCH_SOLVER strategy_solver_binsearcht(\
  *dynamic_cast<tpolyhedra_domaint *>(simple_domains[next_domain++]), \
  solver, \
  SSA.ns)
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
  std::unique_ptr<strategy_solver_baset> s_solver;
  if(template_generator.options.get_bool_option("compute-ranking-functions"))
  {
    if(template_generator.options.get_bool_option(
      "monolithic-ranking-function"))
    {
      s_solver=std::unique_ptr<strategy_solver_baset>(
        new SIMPLE_SOLVER(domain, linrank_domaint));
      result=std::unique_ptr<domaint::valuet>(
        new linrank_domaint::templ_valuet());
    }
    else
    {
      s_solver=std::unique_ptr<strategy_solver_baset>(
        new SIMPLE_SOLVER(domain, lexlinrank_domaint));
      result=std::unique_ptr<domaint::valuet>(
        new lexlinrank_domaint::templ_valuet());
    }
  }
  else
  {
    domaint *invariant_domain;
    // Check if symbolic paths domain is used. If so, invariant_domain points to
    // the inner domain of the symbolic paths domain.
    if(template_generator.options.get_bool_option("sympath"))
      invariant_domain=
        dynamic_cast<sympath_domaint *>(domain)->inner_domain.get();
    else
      invariant_domain=domain;

    // simple_domains contains a vector of pointers to simple domains used.
    // This is either invariant_domain (if a single simple domain is used) or
    // the vector of domains retrieved from the product domain.
    std::vector<domaint *> simple_domains;
    unsigned next_domain=0;
    auto *product_domain=dynamic_cast<product_domaint *>(invariant_domain);
    if(product_domain)
      simple_domains=product_domain->get_domains();
    else
      simple_domains.push_back(invariant_domain);

    // Create list of solvers and values.
    // Important: these must follow the order of domains created in the
    // template generator.
    solver_vect solvers;
    value_vect values;
    if(template_generator.options.get_bool_option("equalities"))
    {
      solvers.emplace_back(
        new SIMPLE_SOLVER(simple_domains[next_domain++], equality_domaint));
      values.emplace_back(new equality_domaint::equ_valuet());
    }
    if(template_generator.options.get_bool_option("heap"))
    {
      solvers.emplace_back(
        new SIMPLE_SOLVER(simple_domains[next_domain++], heap_domaint));
      values.emplace_back(new heap_domaint::heap_valuet());
    }
    if(template_generator.options.get_bool_option("intervals") ||
       template_generator.options.get_bool_option("zones") ||
       template_generator.options.get_bool_option("octagons") ||
       template_generator.options.get_bool_option("qzones"))
    {
      if(template_generator.options.get_bool_option("enum-solver"))
      {
        solvers.emplace_back(
          new SIMPLE_SOLVER(simple_domains[next_domain++], tpolyhedra_domaint));
        values.emplace_back(new tpolyhedra_domaint::templ_valuet());
      }
      else if(template_generator.options.get_bool_option("predabs-solver"))
      {
        solvers.emplace_back(
          new SIMPLE_SOLVER(simple_domains[next_domain++], predabs_domaint));
        values.emplace_back(new predabs_domaint::templ_valuet());
      }
      else if(template_generator.options.get_bool_option("binsearch-solver"))
      {
        solvers.emplace_back(new BINSEARCH_SOLVER);
        values.emplace_back(new tpolyhedra_domaint::templ_valuet());
      }
      else
        assert(false);
    }

    if(solvers.size()==1)
    {
      s_solver=std::move(solvers[0]);
      result=std::move(values[0]);
    }
    else
    {
      s_solver=std::unique_ptr<strategy_solver_baset>(
        new strategy_solver_productt(
          *product_domain, solver, SSA.ns, std::move(solvers)));
      result=std::unique_ptr<domaint::valuet>(
        new product_domaint::valuet(std::move(values)));
    }

    if(template_generator.options.get_bool_option("sympath"))
    {
      s_solver=std::unique_ptr<strategy_solver_baset>(
        new strategy_solver_sympatht(
          *dynamic_cast<sympath_domaint *>(domain),
          solver,
          SSA,
          std::move(s_solver)));
      result=std::unique_ptr<domaint::valuet>(
        new sympath_domaint::sympath_valuet(std::move(result)));
    }
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
}

void ssa_analyzert::get_result(exprt &_result, const var_sett &vars)
{
  domain->project_on_vars(*result, vars, _result);
}
