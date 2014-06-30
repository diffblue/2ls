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

#ifdef DEBUG
#include <iostream>
#endif

/*******************************************************************\

Function: ssa_analyzert::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_analyzert::operator()(local_SSAt &SSA)
{
  if(SSA.goto_function.body.instructions.empty())
    return;

  // handle special functions

  const irep_idt &function_id = SSA.goto_function.body.instructions.front().function;
  bool is_initialize = (id2string(function_id)=="c::__CPROVER_initialize");

  // gather information for creating domains

  var_listt pre_state_vars, post_state_vars;

  domaint::guardst var_pre_guards;
  domaint::guardst var_post_guards;
  domaint::kindst var_kinds;

  var_listt top_vars;
  add_vars(SSA.params,top_vars);
  add_vars(SSA.globals_in,top_vars);
  var_listt vars = top_vars;

  exprt first_guard = SSA.guard_symbol(SSA.goto_function.body.instructions.begin());

  for(unsigned i=0; i<top_vars.size(); ++i) 
  {
    var_pre_guards.push_back(first_guard); //TODO: get first guard
    var_post_guards.push_back(first_guard);
    var_kinds.push_back(domaint::IN);
  }

  // get all backwards edges
  forall_goto_program_instructions(i_it, SSA.goto_function.body)
  {
    if(i_it->is_backwards_goto())
    {
                  
      exprt pre_guard = and_exprt(SSA.guard_symbol(i_it->get_target()), 
        SSA.name(SSA.guard_symbol(), local_SSAt::LOOP_SELECT, i_it));
      exprt post_guard = SSA.guard_symbol(i_it);
      
      const ssa_domaint::phi_nodest &phi_nodes=SSA.ssa_analysis[i_it->get_target()].phi_nodes;
      
      // Record the objects modified by the loop to get
      // 'primed' (post-state) and 'unprimed' (pre-state) variables.
      for(local_SSAt::objectst::const_iterator
          o_it=SSA.ssa_objects.objects.begin();
          o_it!=SSA.ssa_objects.objects.end();
          o_it++)
      {
        ssa_domaint::phi_nodest::const_iterator p_it=
        phi_nodes.find(o_it->get_identifier());

        if(p_it==phi_nodes.end()) continue; // object not modified in this loop

        symbol_exprt in=SSA.name(*o_it, local_SSAt::LOOP_BACK, i_it);
        symbol_exprt out=SSA.read_rhs(*o_it, i_it);
      
        var_pre_guards.push_back(pre_guard);
        var_post_guards.push_back(post_guard);
        var_kinds.push_back(domaint::LOOP);
      
        pre_state_vars.push_back(in);
        post_state_vars.push_back(out);
        
  #ifdef DEBUG
        std::cout << "Adding " << from_expr(ns, "", in) << " " << 
          from_expr(ns, "", out) << std::endl;        
  #endif
     }
    } 
  }
  
#ifdef DEBUG
  for(unsigned i=0; i<pre_state_vars.size(); ++i)
  {
    std::cout << from_expr(pre_state_vars[i]) << " pre-guard:  " << 
      from_expr(var_pre_guards[i]) << std::endl;  
    std::cout << from_expr(pre_state_vars[i]) << " post-guard: " << 
      from_expr(var_post_guards[i]) << std::endl;  
  }
#endif

  template_domaint::templatet templ;
   
  add_vars(pre_state_vars,vars);
  var_listt added_globals_out = add_vars(SSA.globals_out,vars); 

  for(unsigned i=0; i<added_globals_out.size(); ++i) 
  {
    goto_programt::const_targett t = 
      SSA.goto_function.body.instructions.end(); t--;
    exprt guard = SSA.guard_symbol(t);
    var_pre_guards.push_back(true_exprt()); 
    var_post_guards.push_back(guard); 
    var_kinds.push_back(domaint::OUT);
  }
  
  // building map for renaming from pre into post-state
  assert(pre_state_vars.size()==post_state_vars.size());
  var_listt::const_iterator it1=pre_state_vars.begin();
  var_listt::const_iterator it2=post_state_vars.begin();
  for(; it1!=pre_state_vars.end(); ++it1, ++it2)
  {
    renaming_map[*it1]=*it2;    
  }

  #ifdef DEBUG
  std::cout << "**** Function stats *****" << std::endl;
  std::cout << "  var size " << vars.size() << std::endl
            << "  params size " << SSA.params.size() << std::endl
            << "  pre_state " << pre_state_vars.size() << std::endl;
  #endif  

  //get domain from command line options
  if(options.get_bool_option("intervals") || is_initialize)
  {
    template_domaint::make_interval_template(templ, vars, 
      var_pre_guards, var_post_guards, var_kinds, ns);
  }
  else if(options.get_bool_option("zones"))
  {
    template_domaint::make_zone_template(templ, vars, 
      var_pre_guards, var_post_guards, var_kinds, ns); 
  }
  else if(options.get_bool_option("octagons"))
  {
    template_domaint::make_octagon_template(templ, vars, 
      var_pre_guards, var_post_guards, var_kinds, ns); 
  }
  else if(options.get_bool_option("equalities"))
  {
    //nothing to do
  }
  else assert(false);
  
  constraintst transition_relation;
  transition_relation << SSA;

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
  domaint *domain; 
  strategy_solver_baset::invariantt *inv;
  if(options.get_bool_option("equalities") && !is_initialize)
  {
    domain = new equality_domaint(vars, 
      var_pre_guards, var_post_guards, var_kinds, ns);
    strategy_solver = new strategy_solver_equalityt(
        transition_relation, renaming_map,
        *static_cast<equality_domaint *>(domain), solver, ns);
    inv = new equality_domaint::equ_valuet();
  }
  else
  {
    inv = new template_domaint::templ_valuet();
    if(options.get_bool_option("enum-solver") || is_initialize)
    {
      domain = new template_domaint(templ);
      strategy_solver = new strategy_solver_enumerationt(
        transition_relation, renaming_map,
        *static_cast<template_domaint *>(domain), solver, ns);
    }
    else if(options.get_bool_option("binsearch-solver"))
    {
      domain = new template_domaint(templ);
      strategy_solver = new strategy_solver_binsearcht(
        transition_relation, renaming_map,
        *static_cast<template_domaint *>(domain), solver, ns);
    }
    else assert(false);
  }

  strategy_solver->set_message_handler(get_message_handler());
  strategy_solver->set_verbosity(get_verbosity());

#if 1
  domain->output_domain(debug(), ns); debug() << eom;
#endif  


  iteration_number=0;


  // initialize inv
  domain->initialize(*inv);

  bool change;

  do
  {
    iteration_number++;
    
    #ifdef DEBUG
    std::cout << "\n"
              << "******** Forward least fixed-point iteration #"
              << iteration_number << "\n";
    #endif
   
    change = strategy_solver->iterate(*inv);

    if(change) 
    {

      #ifdef DEBUG
      std::cout << "Value after " << iteration_number
            << " iteration(s):\n";
      domain->output_value(std::cout,*inv,ns);
      #endif
    }
  }
  while(change);

  #ifdef DEBUG
  std::cout << "Fixed-point after " << iteration_number
            << " iteration(s)\n";
  domain->output_value(std::cout,*inv,ns);
  #endif

  domain->project_on_inout(*inv,inv_inout);
  domain->project_on_loops(*inv,inv_loop);
  delete strategy_solver;
  delete inv;
  delete domain;
}

void ssa_analyzert::get_summary(exprt &result)
{
  result = inv_inout;
}

void ssa_analyzert::get_loop_invariants(exprt &result) 
{
  result = inv_loop;
}

bool ssa_analyzert::add_vars_filter(const symbol_exprt &s)
{
  return s.type().id()==ID_unsignedbv || s.type().id()==ID_signedbv ||
    s.type().id()==ID_floatbv;
}

ssa_analyzert::var_listt ssa_analyzert::add_vars(const local_SSAt::var_listt &vars_to_add, 
    var_listt &vars)
{
  var_listt vars_added;
  for(local_SSAt::var_listt::const_iterator it = vars_to_add.begin();
      it != vars_to_add.end(); it++)
  {
    if(add_vars_filter(*it)) { vars.push_back(*it); vars_added.push_back(*it); }
  }
  return vars_added;
}

ssa_analyzert::var_listt ssa_analyzert::add_vars(const local_SSAt::var_sett &vars_to_add, 
    var_listt &vars)
{
  var_listt vars_added;
  for(local_SSAt::var_sett::const_iterator it = vars_to_add.begin();
      it != vars_to_add.end(); it++)
  {
    if(add_vars_filter(*it)) { vars.push_back(*it); vars_added.push_back(*it); }
  }
  return vars_added;
}

ssa_analyzert::var_listt ssa_analyzert::add_vars(const var_listt &vars_to_add, 
    var_listt &vars)
{
  var_listt vars_added;
  for(var_listt::const_iterator it = vars_to_add.begin();
      it != vars_to_add.end(); it++)
  {
    if(add_vars_filter(*it)) { vars.push_back(*it); vars_added.push_back(*it); }
  }
  return vars_added;
}
