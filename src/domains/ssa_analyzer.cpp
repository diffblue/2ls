/*******************************************************************\

Module: SSA Analyzer

Author: Peter Schrammel

\*******************************************************************/

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
#include "strategy_solver_enumeration.h"
#include "strategy_solver_binsearch.h"
#include "strategy_solver_binsearch2.h"
#include "strategy_solver_binsearch3.h"
#include "strategy_solver_equality.h"
#include "linrank_domain.h"
#include "lexlinrank_domain.h"
#include "ranking_solver_enumeration.h"
#include "lexlinrank_solver_enumeration.h"
#include "template_generator_ranking.h"
#include "strategy_solver_predabs.h"
#include "ssa_analyzer.h"
#include "strategy_solver_heap.h"
#include "strategy_solver_heap_interval.h"

#define BINSEARCH_SOLVER strategy_solver_binsearcht(\
  *static_cast<tpolyhedra_domaint *>(domain), solver, SSA.ns)
#if 0
#define BINSEARCH_SOLVER strategy_solver_binsearch2t(\
  *static_cast<tpolyhedra_domaint *>(domain), solver, SSA.ns)
#define BINSEARCH_SOLVER strategy_solver_binsearch3t(\
  *static_cast<tpolyhedra_domaint *>(domain), solver, SSA, SSA.ns)
#endif

/*******************************************************************\

Function: ssa_analyzert::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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
  strategy_solver_baset *strategy_solver;
  if(template_generator.options.get_bool_option("compute-ranking-functions"))
  {
    if(template_generator.options.get_bool_option(
         "monolithic-ranking-function"))
    {
      strategy_solver=new ranking_solver_enumerationt(
        *static_cast<linrank_domaint *>(domain), solver, SSA.ns,
        template_generator.options.get_unsigned_int_option(
          "max-inner-ranking-iterations"));
      result=new linrank_domaint::templ_valuet();
    }
    else
    {
      strategy_solver=new lexlinrank_solver_enumerationt(
        *static_cast<lexlinrank_domaint *>(domain), solver, SSA.ns,
        template_generator.options.get_unsigned_int_option(
          "lexicographic-ranking-function"),
        template_generator.options.get_unsigned_int_option(
          "max-inner-ranking-iterations"));
      result=new lexlinrank_domaint::templ_valuet();
    }
  }
  else if(template_generator.options.get_bool_option("equalities"))
  {
    strategy_solver=new strategy_solver_equalityt(
      *static_cast<equality_domaint *>(domain), solver, SSA.ns);
    result=new equality_domaint::equ_valuet();
  }
  else if(template_generator.options.get_bool_option("heap"))
  {
    strategy_solver=new strategy_solver_heapt(
      *static_cast<heap_domaint *>(domain),
      solver,
      SSA,
      precondition,
      get_message_handler(),
      template_generator);
    result=new heap_domaint::heap_valuet();
  }
  else if(template_generator.options.get_bool_option("heap-interval"))
  {
    strategy_solver=new strategy_solver_heap_intervalt(
      *static_cast<heap_interval_domaint *>(domain),
      solver,
      SSA,
      precondition,
      get_message_handler(),
      template_generator);
    result=new heap_interval_domaint::heap_interval_valuet();
  }
  else
  {
    if(template_generator.options.get_bool_option("enum-solver"))
    {
      result=new tpolyhedra_domaint::templ_valuet();
      strategy_solver=new strategy_solver_enumerationt(
        *static_cast<tpolyhedra_domaint *>(domain), solver, SSA.ns);
    }
    else if(template_generator.options.get_bool_option("predabs-solver"))
    {
      result=new predabs_domaint::templ_valuet();
      strategy_solver=new strategy_solver_predabst(
        *static_cast<predabs_domaint *>(domain), solver, SSA.ns);
    }
    else if(template_generator.options.get_bool_option("binsearch-solver"))
    {
      result=new tpolyhedra_domaint::templ_valuet();
      strategy_solver=new BINSEARCH_SOLVER;
    }
    else
      assert(false);
  }

  strategy_solver->set_message_handler(get_message_handler());

  // initialize inv
  domain->initialize(*result);

  // iterate
  while(strategy_solver->iterate(*result)) {}

  solver.pop_context();

  // statistics
  solver_instances+=strategy_solver->get_number_of_solver_instances();
  solver_calls+=strategy_solver->get_number_of_solver_calls();
  solver_instances+=strategy_solver->get_number_of_solver_instances();

  delete strategy_solver;
}

/*******************************************************************\

Function: ssa_analyzert::get_result

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_analyzert::get_result(exprt &_result, const domaint::var_sett &vars)
{
  domain->project_on_vars(*result, vars, _result);
}

/*******************************************************************\

Function: ssa_analyzert::update_heap_out

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
void ssa_analyzert::update_heap_out(summaryt::var_sett &out)
{
  heap_domaint &heap_domain=static_cast<heap_domaint &>(*domain);

  auto new_heap_vars=heap_domain.get_new_heap_vars();
  out.insert(new_heap_vars.begin(), new_heap_vars.end());
}

/*******************************************************************\

Function: ssa_analyzert::input_heap_bindings

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
const exprt ssa_analyzert::input_heap_bindings()
{
  return static_cast<heap_domaint &>(*domain).get_iterator_bindings();
}
