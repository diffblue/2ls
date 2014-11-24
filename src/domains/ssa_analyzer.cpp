/*******************************************************************\

Module: Data Flow Analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

//#define DEBUG

#include <util/options.h>


#include "strategy_solver_base.h"
#include "strategy_solver_enumeration.h"
//#include "solver_enumeration.h"
#include "strategy_solver_binsearch.h"
#include "strategy_solver_binsearch2.h"
#include "strategy_solver_binsearch3.h"
#include "strategy_solver_equality.h"
#include "ssa_analyzer.h"

#include <solvers/sat/satcheck.h>
#include <solvers/flattening/bv_pointers.h>

#include <util/find_symbols.h>
#include <util/arith_tools.h>
#include <util/simplify_expr.h>
#include <util/mp_arith.h>

#define BINSEARCH_SOLVER strategy_solver_binsearcht(*static_cast<tpolyhedra_domaint *>(domain), solver, SSA.ns)
//#define BINSEARCH_SOLVER strategy_solver_binsearch2t(*static_cast<tpolyhedra_domaint *>(domain), solver, SSA.ns)
//#define BINSEARCH_SOLVER strategy_solver_binsearch3t(*static_cast<tpolyhedra_domaint *>(domain), solver, SSA, SSA.ns)

#ifdef DEBUG
#include <iostream>
#endif

/*******************************************************************\

Function: ssa_analyzert::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_analyzert::operator()(incremental_solvert &solver,
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
  
  domain = template_generator.domain();

  // get strategy solver from options
  strategy_solver_baset *strategy_solver;
  if(template_generator.options.get_bool_option("equalities"))
  {
    strategy_solver = new strategy_solver_equalityt(
        *static_cast<equality_domaint *>(domain), solver, SSA.ns);    
    result = new equality_domaint::equ_valuet();
  }
  else
  {
    result = new tpolyhedra_domaint::templ_valuet();
    if(template_generator.options.get_bool_option("enum-solver"))
    {
      strategy_solver = new strategy_solver_enumerationt(
        *static_cast<tpolyhedra_domaint *>(domain), solver, SSA.ns);
    }
    else if(template_generator.options.get_bool_option("binsearch-solver"))
    {
      strategy_solver = 
        new BINSEARCH_SOLVER;
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

  solver.pop_context();

  //statistics
  solver_calls += strategy_solver->get_number_of_solver_calls();
  solver_instances += strategy_solver->get_number_of_solver_instances();

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
