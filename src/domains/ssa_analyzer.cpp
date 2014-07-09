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

void ssa_analyzert::operator()(local_SSAt &SSA, const exprt &precondition)
{
  if(SSA.goto_function.body.instructions.empty())
    return;

  // handle special functions
  const irep_idt &function_id = SSA.goto_function.body.instructions.front().function;
  bool is_initialize = (id2string(function_id)=="c::__CPROVER_initialize");

  // gather information for creating domains
  domaint::var_specst var_specs;
  collect_variables(SSA, var_specs);

  //get domain from command line options
  template_domaint::templatet templ;
  templ.clear();
  if(options.get_bool_option("intervals") || is_initialize)
  {
    domaint::var_specst new_var_specs = filter_template_domain(var_specs);
    template_domaint::add_interval_template(templ, new_var_specs, ns);
  }
  else if(options.get_bool_option("zones"))
  {
    domaint::var_specst new_var_specs = filter_template_domain(var_specs);
    template_domaint::add_zone_template(templ, new_var_specs, ns); 
  }
  else if(options.get_bool_option("octagons"))
  {
    domaint::var_specst new_var_specs = filter_template_domain(var_specs);
    template_domaint::add_octagon_template(templ, new_var_specs, ns); 
  }
  else if(options.get_bool_option("equalities"))
  {
    //nothing to do
  }
  else assert(false);
  
  // convert SSA to transition relation
  constraintst transition_relation;
  transition_relation << SSA;

  // add precondition
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
  domaint *domain; 
  strategy_solver_baset::invariantt *inv;
  if(options.get_bool_option("equalities") && !is_initialize)
  {
    domaint::var_specst new_var_specs = filter_equality_domain(var_specs);
    domain = new equality_domaint(new_var_specs, ns);
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

/*******************************************************************\

Function: ssa_analyzert::get_summary

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_analyzert::get_summary(exprt &result)
{
  result = inv_inout;
}

/*******************************************************************\

Function: ssa_analyzert::get_loop_invariants

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_analyzert::get_loop_invariants(exprt &result) 
{
  result = inv_loop;
}

/*******************************************************************\

Function: ssa_analyzert::get_calling_contexts

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_analyzert::get_calling_contexts(calling_contextst &result)
{
  assert(compute_calling_contexts);
  result = calling_contexts;
}

/*******************************************************************\

Function: ssa_analyzert::collect_variables

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_analyzert::collect_variables(const local_SSAt &SSA,
				      domaint::var_specst &var_specs)
{
  var_specs.clear();

  // add params and globals_in
  exprt first_guard = SSA.guard_symbol(SSA.goto_function.body.instructions.begin());
  add_vars(SSA.params,first_guard,first_guard,domaint::IN,var_specs);
  add_vars(SSA.globals_in,first_guard,first_guard,domaint::IN,var_specs);

  // used for renaming map
  var_listt pre_state_vars, post_state_vars;

  // add loop variables
  forall_goto_program_instructions(i_it, SSA.goto_function.body)
  {
    if(i_it->is_backwards_goto())
    {
      exprt pre_guard = and_exprt(SSA.guard_symbol(i_it->get_target()), 
        SSA.name(SSA.guard_symbol(), local_SSAt::LOOP_SELECT, i_it));
      exprt post_guard = SSA.guard_symbol(i_it);
      
      const ssa_domaint::phi_nodest &phi_nodes = 
        SSA.ssa_analysis[i_it->get_target()].phi_nodes;
      
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

        add_var(in,pre_guard,post_guard,domaint::LOOP,var_specs);
      
        pre_state_vars.push_back(in);
        post_state_vars.push_back(out);
        
  #ifdef DEBUG
        std::cout << "Adding " << from_expr(ns, "", in) << " " << 
          from_expr(ns, "", out) << std::endl;        
  #endif
     }

      /*
      // local nondet variables
      const ssa_domaint &ssa_domain=SSA.ssa_analysis[i_it->get_target()];
      for(local_SSAt::objectst::const_iterator
          o_it=SSA.ssa_objects.objects.begin();
          o_it!=SSA.ssa_objects.objects.end();
          o_it++)
      {
        ssa_domaint::def_mapt::const_iterator 
          d_it = ssa_domain.def_map.find(o_it->get_identifier());
	if(d_it!=ssa_domain.def_map.end()) 
	{
  #if 1
        std::cout << "ssa_object " << o_it->get_identifier() <<
		  ": " << d_it->second.def.is_input() << std::endl;        
  #endif
	  symbol_exprt in=SSA.name_input(*o_it);
          exprt guard = SSA.guard_symbol(i_it->get_target());
	  add_var(in,guard,guard,domaint::IN,var_specs);

  #if 1
          std::cout << "Adding " << from_expr(ns, "", in) << std::endl;        
  #endif
	}
      }
      */
    } 
  }
  
  /*
  // collect context variables to track //TODO: create domain var data structure
  for(local_SSAt::nodest::iterator n = SSA.nodes.begin(); 
      n!=SSA.nodes.end(); n++)
  {
    for(local_SSAt::nodet::function_callst::iterator 
        f_it = n->second.function_calls.begin();
        f_it != n->second.function_calls.end(); f_it++)
    {
      assert(f_it->function().id()==ID_symbol); //no function pointers

      //getting globals at call site
      SSA.get_globals(n->first,cs_globals_in[f_it]);

      //add function arguments
      for(exprt::operandst::const_iterator it =  f_it->arguments().begin();
          it !=  f_it->arguments().end(); it++)
      {
	std::set<symbol_exprt> symbols;
	find_symbols(*it,symbols);        
	context_vars[f_it].insert(symbols.begin(),symbols.end());
      }
    }
  }
   */


#ifdef DEBUG
  for(unsigned i=0; i<pre_state_vars.size(); ++i)
  {
    std::cout << from_expr(pre_state_vars[i]) << " pre-guard:  " << 
      from_expr(pre_guards[i]) << std::endl;  
    std::cout << from_expr(pre_state_vars[i]) << " post-guard: " << 
      from_expr(post_guards[i]) << std::endl;  
  }
#endif

  // add globals_out (includes return values)
  exprt last_guard = SSA.guard_symbol(--SSA.goto_function.body.instructions.end());
  add_vars(SSA.globals_out,last_guard,last_guard,domaint::OUT,var_specs);
  
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

  debug() << "Template variables: " << eom;
  domaint::output_var_specs(debug(),var_specs,SSA.ns); debug() << eom;

}

/*******************************************************************\

Function: ssa_analyzert::filter_template_domain

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

domaint::var_specst ssa_analyzert::filter_template_domain(
  const domaint::var_specst& var_specs)
{
  domaint::var_specst new_var_specs;
  for(domaint::var_specst::const_iterator v = var_specs.begin(); 
      v!=var_specs.end(); v++)
  {
    const domaint::vart &s = v->var;
    if(s.type().id()==ID_unsignedbv || s.type().id()==ID_signedbv ||
       s.type().id()==ID_floatbv)
    {
      new_var_specs.push_back(*v);
    }
  }
  return new_var_specs;
}

/*******************************************************************\

Function: ssa_analyzert::filter_equality_domain

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

domaint::var_specst ssa_analyzert::filter_equality_domain(
  const domaint::var_specst& var_specs)
{
  domaint::var_specst new_var_specs;
  for(domaint::var_specst::const_iterator v = var_specs.begin(); 
      v!=var_specs.end(); v++)
  {
    new_var_specs.push_back(*v);
  }
  return new_var_specs;
}

/*******************************************************************\

Function: ssa_analyzert::add_vars

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_analyzert::add_var(const domaint::vart &var, 
			    const domaint::guardt &pre_guard, 
			    const domaint::guardt &post_guard,
			    const domaint::kindt &kind,
			    domaint::var_specst &var_specs)
{
  if(var.type().id()!=ID_array)
  {
    var_specs.push_back(domaint::var_spect());
    domaint::var_spect &var_spec = var_specs.back();
    var_spec.pre_guard = pre_guard;
    var_spec.post_guard = post_guard;
    var_spec.kind = kind;
    var_spec.var = var;
  }

  //arrays
  if(var.type().id()==ID_array && options.get_bool_option("arrays"))
  {
    const array_typet &array_type = to_array_type(var.type());
    mp_integer size;
    to_integer(array_type.size(), size);
    for(mp_integer i=0; i<size; i=i+1) 
    {
      var_specs.push_back(domaint::var_spect());
      domaint::var_spect &var_spec = var_specs.back();
      constant_exprt index = from_integer(i,array_type.size().type());
      var_spec.pre_guard = pre_guard;
      var_spec.post_guard = post_guard;
      var_spec.kind = kind;
      var_spec.var = index_exprt(var,index);
    }
  }
}

void ssa_analyzert::add_vars(const local_SSAt::var_listt &vars_to_add, 
			     const domaint::guardt &pre_guard, 
			     const domaint::guardt &post_guard,
			     const domaint::kindt &kind,
			     domaint::var_specst &var_specs)
{
  for(local_SSAt::var_listt::const_iterator it = vars_to_add.begin();
      it != vars_to_add.end(); it++) 
    add_var(*it,pre_guard,post_guard,kind,var_specs);
}

void ssa_analyzert::add_vars(const local_SSAt::var_sett &vars_to_add, 
			     const domaint::guardt &pre_guard, 
			     const domaint::guardt &post_guard,
			     const domaint::kindt &kind,
			     domaint::var_specst &var_specs)
{
  for(local_SSAt::var_sett::const_iterator it = vars_to_add.begin();
      it != vars_to_add.end(); it++)
    add_var(*it,pre_guard,post_guard,kind,var_specs);
}

void ssa_analyzert::add_vars(const var_listt &vars_to_add, 
			     const domaint::guardt &pre_guard, 
			     const domaint::guardt &post_guard,
			     const domaint::kindt &kind,
			     domaint::var_specst &var_specs)
{
  for(var_listt::const_iterator it = vars_to_add.begin();
      it != vars_to_add.end(); it++)
    add_var(*it,pre_guard,post_guard,kind,var_specs);
}
