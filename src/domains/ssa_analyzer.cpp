/*******************************************************************\

Module: Data Flow Analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

//#define DEBUG

#include <util/options.h>


#include "strategy_solver_base.h"
#include "strategy_solver_enumeration.h"
#include "strategy_solver_binsearch.h"
#include "strategy_solver_equality.h"
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

  // handle special functions
  const irep_idt &function_id = SSA.goto_function.body.instructions.front().function;
  bool is_initialize = (id2string(function_id)=="c::__CPROVER_initialize");
  
  // convert SSA to transition relation
  constraintst transition_relation;
  transition_relation << SSA;

  // TODO: must be made incremental in future
  transition_relation.push_back(SSA.get_enabling_exprs());

  // add precondition (or conjunction of asssertion in backward analysis)
  transition_relation.push_back(precondition);

#ifdef DEBUG
  for(constraintst::const_iterator it = transition_relation.begin(); 
    it != transition_relation.end(); it++)
  {
    std::set<symbol_exprt> symbols;
    find_symbols(*it,symbols);

    for(std::set<symbol_exprt>::const_iterator s_it = symbols.begin(); 
      s_it != symbols.end(); s_it++)
    {
      if(renaming_map.find(*s_it)==renaming_map.end())
      {
        renaming_map[*s_it] = *s_it;  
      }
    }
  }  
#endif
  
  // solver
  //TODO: get backend solver from options
  satcheck_minisat_no_simplifiert satcheck;
  bv_pointerst solver(ns, satcheck);

  // get strategy solver from options
  strategy_solver_baset *strategy_solver;
  if(options.get_bool_option("equalities") && !is_initialize)
  {
    template_generator.filter_equality_domain();
    domain = new equality_domaint(template_generator.renaming_map, template_generator.var_specs, ns);
    strategy_solver = new strategy_solver_equalityt(
        transition_relation, 
        *static_cast<equality_domaint *>(domain), solver, ns);    
    result = new equality_domaint::equ_valuet();
  }
  else
  {
    result = new template_domaint::templ_valuet();
    if(options.get_bool_option("enum-solver") || is_initialize)
    {
      domain = new template_domaint(template_generator.renaming_map);
      strategy_solver = new strategy_solver_enumerationt(
        transition_relation, 
        *static_cast<template_domaint *>(domain), solver, ns);
    }
    else if(options.get_bool_option("binsearch-solver"))
    {
      domain = new template_domaint(template_generator.renaming_map);
      strategy_solver = new strategy_solver_binsearcht(
        transition_relation, 
        *static_cast<template_domaint *>(domain), solver, ns);
    }
    else assert(false);
  }

  //get domain from command line options
  if(options.get_bool_option("intervals") || is_initialize)
  {
    template_generator.filter_template_domain();
    static_cast<template_domaint *>(domain)->add_interval_template(
      template_generator.var_specs, ns);
  }
  else if(options.get_bool_option("zones"))
  {
    template_generator.filter_template_domain();
    static_cast<template_domaint *>(domain)->add_zone_template(
      template_generator.var_specs, ns);
  }
  else if(options.get_bool_option("octagons"))
  {
    template_generator.filter_template_domain();
    static_cast<template_domaint *>(domain)->add_octagon_template(
      template_generator.var_specs, ns);
  }

  strategy_solver->set_message_handler(get_message_handler());

#if 1
  debug() << "Template: " << eom;
  domain->output_domain(debug(), ns); debug() << eom;
#endif  


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
      domain->output_value(std::cout,*result,ns);
      #endif
    }
  }
  while(change);

  #ifdef DEBUG
  std::cout << "Fixed-point after " << iteration_number
            << " iteration(s)\n";
  domain->output_value(std::cout,*result,ns);
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
