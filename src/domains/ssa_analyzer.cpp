/*******************************************************************\

Module: Data Flow Analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

//#define DEBUG

#include <util/options.h>


#include "strategy_solver_base.h"
#include "strategy_solver_enumeration.h"
#include "strategy_solver_binsearch.h"
#include "strategy_solver_binsearch2.h"

#include "strategy_solver_equality.h"
#include "linrank_domain.h"
#include "lexlinrank_domain.h"
#include "ranking_solver_enumeration.h"
#include "lexlinrank_solver_enumeration.h"
#include "template_generator_ranking.h"

#include "ssa_analyzer.h"


#include <solvers/sat/satcheck.h>
#include <solvers/flattening/bv_pointers.h>

#include <util/find_symbols.h>
#include <util/arith_tools.h>
#include <util/simplify_expr.h>
#include <util/mp_arith.h>

#ifdef DEBUG
#include <iostream>
#endif

/*******************************************************************\

Function: ssa_analyzert::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_analyzert::operator()(local_SSAt &SSA, 
                               const exprt &precondition,
                               template_generator_baset &template_generator)
{
  if(SSA.goto_function.body.instructions.empty())
    return;
  
  // convert SSA to transition relation
  constraintst transition_relation;
  transition_relation << SSA;

  // TODO: must be made incremental in future
  transition_relation.push_back(SSA.get_enabling_exprs());

  // add precondition (or conjunction of asssertion in backward analysis)
  transition_relation.push_back(precondition);
  
  // solver
  //TODO: get backend solver from options
  satcheck_minisat_no_simplifiert satcheck;
  bv_pointerst solver(SSA.ns, satcheck);

  domain = template_generator.domain();

  // get strategy solver from options
  strategy_solver_baset *strategy_solver;
  if(template_generator.options.get_bool_option("compute-ranking-functions"))
  {
#ifndef LEXICOGRAPHIC
    strategy_solver = new ranking_solver_enumerationt(
        transition_relation, 
        *static_cast<linrank_domaint *>(domain), solver, SSA.ns);    
    result = new linrank_domaint::templ_valuet();
#else
    strategy_solver = new lexlinrank_solver_enumerationt(
        transition_relation, 
        *static_cast<lexlinrank_domaint *>(domain), solver, SSA.ns);    
    result = new lexlinrank_domaint::templ_valuet();
#endif
  }  
  else if(template_generator.options.get_bool_option("equalities"))
  {
    strategy_solver = new strategy_solver_equalityt(
        transition_relation, 
        *static_cast<equality_domaint *>(domain), solver, SSA.ns);    
    result = new equality_domaint::equ_valuet();
  }
  else
  {
    result = new tpolyhedra_domaint::templ_valuet();
    if(template_generator.options.get_bool_option("enum-solver"))
    {
      strategy_solver = new strategy_solver_enumerationt(
        transition_relation, 
        *static_cast<tpolyhedra_domaint *>(domain), solver, SSA.ns);
    }
    else if(template_generator.options.get_bool_option("binsearch-solver"))
    {
      strategy_solver = 
#ifndef BINSEARCH_SUM
        new strategy_solver_binsearcht(
#else
        new strategy_solver_binsearch2t(
#endif
        transition_relation, 
        *static_cast<tpolyhedra_domaint *>(domain), solver, SSA.ns);
    }
    else assert(false);
  }

  strategy_solver->set_message_handler(get_message_handler());

  unsigned iteration_number=0;

  // initialize inv
  domain->initialize(*result);

  bool change;

  do
  {
    iteration_number++;
    
    #ifdef DEBUG
    std::cout << "\n"
              << "******** Forward least fixed-point iteration #"
              << iteration_number << "\n";
    #endif
   
    change = strategy_solver->iterate(*result);

    if(change) 
    {

      #ifdef DEBUG
      std::cout << "Value after " << iteration_number
            << " iteration(s):\n";
      domain->output_value(std::cout,*result,SSA.ns);
      #endif
    }
  }
  while(change);

  #ifdef DEBUG
  std::cout << "Fixed-point after " << iteration_number
            << " iteration(s)\n";
  domain->output_value(std::cout,*result,SSA.ns);
  #endif

  //statistics
  solver_calls += strategy_solver->get_number_of_solver_calls();

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
  domain->project_on_vars(*result,vars,_result);
}
