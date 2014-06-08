/*******************************************************************\

Module: Data Flow Analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#define DEBUG

#include "fixed_point.h"
#include "ssa_fixed_point.h"

#ifdef DEBUG
#include <iostream>
#endif

/*******************************************************************\

Function: ssa_fixed_point

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_fixed_point(local_SSAt &SSA, const namespacet &ns)
{
  fixed_pointt fixed_point(ns);

  // get all backwards edges
  
  typedef std::map<goto_programt::const_targett, predicatet::state_var_listt> var_mapt;
  var_mapt var_map;

  forall_goto_program_instructions(i_it, SSA.goto_function.body)
  {
    if(i_it->is_backwards_goto())
    {
      predicatet::state_var_listt &vars=var_map[i_it];
    
      // Record the objects modified by the loop to get
      // 'primed' (post-state) and 'unprimed' (pre-state) variables.
      for(local_SSAt::objectst::const_iterator
          o_it=SSA.ssa_objects.objects.begin();
          o_it!=SSA.ssa_objects.objects.end();
          o_it++)
      {
        symbol_exprt in=SSA.name(*o_it, local_SSAt::LOOP_BACK, i_it);
        symbol_exprt out=SSA.read_rhs(*o_it, i_it);
      
        fixed_point.pre_state_vars.push_back(in);
        fixed_point.post_state_vars.push_back(out);
        vars.push_back(out);
      }

      {
        ssa_objectt guard=SSA.guard_symbol();
        symbol_exprt in=SSA.name(guard, local_SSAt::LOOP_BACK, i_it);
        symbol_exprt out=SSA.name(guard, local_SSAt::OUT, i_it);
        
        fixed_point.pre_state_vars.push_back(in);
        fixed_point.post_state_vars.push_back(out);
        vars.push_back(out);
      }
    }
  }

  // transition relation
  fixed_point.transition_relation << SSA;

  // kick off fixed-point computation
  fixed_point();
  
  // add fixed-point as constraints back into SSA
  for(var_mapt::const_iterator
      v_it=var_map.begin();
      v_it!=var_map.end();
      v_it++)
  {
    
  }
}
