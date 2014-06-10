/*******************************************************************\

Module: Data Flow Analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#define DEBUG

#include <util/options.h>

#include "strategy_solver_base.h"
#include "strategy_solver_enumeration.h"
#include "strategy_solver_binsearch.h"
#include "ssa_analyzer.h"

#include <solvers/sat/satcheck.h>
#include <solvers/flattening/bv_pointers.h>


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

    var_listt pre_state_vars, post_state_vars;

  // get all backwards edges
  forall_goto_program_instructions(i_it, SSA.goto_function.body)
  {
    if(i_it->is_backwards_goto())
    {
      // Record the objects modified by the loop to get
      // 'primed' (post-state) and 'unprimed' (pre-state) variables.
      for(local_SSAt::objectst::const_iterator
          o_it=SSA.ssa_objects.objects.begin();
          o_it!=SSA.ssa_objects.objects.end();
          o_it++)
      {
        symbol_exprt in=SSA.name(*o_it, local_SSAt::LOOP_BACK, i_it);
        symbol_exprt out=SSA.read_rhs(*o_it, i_it);
      
        pre_state_vars.push_back(in);
        post_state_vars.push_back(out);
      }

      {
        ssa_objectt guard=SSA.guard_symbol();
        symbol_exprt in=SSA.name(guard, local_SSAt::LOOP_BACK, i_it);
        symbol_exprt out=SSA.name(guard, local_SSAt::OUT, i_it);
        
        pre_state_vars.push_back(in);
        post_state_vars.push_back(out);
      }
    }
  }

  constraintst transition_relation;
  transition_relation << SSA;

  template_domaint::templatet templ;
  var_listt vars = pre_state_vars;
  //vars.insert(SSA.params.begin(),SSA.params.end());
  //vars.insert(SSA.returns.begin(),SSA.returns.end());
  //vars.insert(SSA.globals_in.begin(),SSA.globals_in.end());
  //vars.insert(SSA.globals_out.begin(),SSA.globals_out.end());
  
  if(options.get_bool_option("intervals"))
  {
    make_interval_template(templ, vars);
  }
  else if(options.get_bool_option("octagons"))
  {
    make_octagon_template(templ, vars); 
  }
  else
  {
    make_interval_template(templ, vars); // default
  }
    
  template_domaint template_domain(templ);

  // solver
  satcheckt satcheck;//TODO: get solver from options
  bv_pointerst solver(ns, satcheck);
  
  //satcheck.set_message_handler(get_message_handler());
  //solver.set_message_handler(get_message_handler()); 

  //TODO: get strategy solver from options
  strategy_solver_enumerationt strategy_solver(transition_relation, pre_state_vars, post_state_vars,
					template_domain, solver);

  iteration_number=0;
  
  bool change;

  do
  {
    iteration_number++;
    
    #ifdef DEBUG
    std::cout << "\n"
              << "******** Forward least fixed-point iteration #"
              << iteration_number << "\n";
    #endif
   
    strategy_solver_baset::strategyt strategy;
    change = strategy_solver.improve(inv,strategy);

    if(change) strategy_solver.solve(inv,strategy);
  }
  while(change);

  #ifdef DEBUG
  std::cout << "Fixed-point after " << iteration_number
            << " iteration(s)\n";
  template_domain.output_value(std::cout,inv,ns);
  #endif
}
