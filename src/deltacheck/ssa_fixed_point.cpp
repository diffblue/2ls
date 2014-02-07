/*******************************************************************\

Module: Data Flow Analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#define DEBUG

#include <solvers/sat/satcheck.h>
#include <solvers/flattening/bv_pointers.h>

#include "ssa_fixed_point.h"

#ifdef DEBUG
#include <iostream>
#endif

/*******************************************************************\

Function: ssa_fixed_pointt::tie_inputs_together

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_fixed_pointt::tie_inputs_together(std::list<exprt> &dest)
{
  // the following are inputs:
  // 1) the parameters of the functions
  // 2) any global objects mentioned
  // 3) the guard at the entry point

  if(SSA_old.goto_function.body.empty() ||
     SSA_new.goto_function.body.empty())
    return;
    
  // 1) function parameters
  
  const code_typet::parameterst &p_new=
    SSA_new.goto_function.type.parameters();
    
  const code_typet::parameterst &p_old=
    SSA_old.goto_function.type.parameters();

  for(unsigned p=0; p<p_new.size(); p++)
    if(p<p_old.size() &&
       p_old[p].type()==p_new[p].type())
    {
      symbol_exprt s_old(p_old[p].get_identifier(), p_old[p].type());
      symbol_exprt s_new(p_new[p].get_identifier(), p_new[p].type());
      s_old=SSA_old.name_input(ssa_objectt(s_old));
      s_new=SSA_new.name_input(ssa_objectt(s_new));

      dest.push_back(equal_exprt(s_old, s_new));
    }
    
  // 2) globals
  
  for(local_SSAt::objectst::const_iterator
      it=SSA_new.assignments.objects.begin();
      it!=SSA_new.assignments.objects.end();
      it++)
  {
    if(!SSA_new.has_static_lifetime(*it))
      continue;
      
    if(SSA_old.assignments.objects.find(*it)==
       SSA_old.assignments.objects.end())
      continue;
    
    symbol_exprt s_new=SSA_new.name_input(*it);
    symbol_exprt s_old=SSA_old.name_input(*it);

    dest.push_back(equal_exprt(s_old, s_new));
  }

  // 3) guard
  
  /*
  dest.set_to_true(
    equal_exprt(SSA_old.guard_symbol(l_old),
                SSA_new.guard_symbol(l_new)));
  */
}

/*******************************************************************\

Function: ssa_fixed_pointt::do_backwards_edge

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_fixed_pointt::do_backwards_edge(
  const local_SSAt &SSA,
  locationt from)
{
  assert(from->is_backwards_goto());
  
  //locationt to=from->get_target();

  // Record the objects modified by the loop to get
  // 'primed' (post-state) and 'unprimed' (pre-state) variables.
  for(local_SSAt::objectst::const_iterator
      o_it=SSA.assignments.objects.begin();
      o_it!=SSA.assignments.objects.end();
      o_it++)
  {
    symbol_exprt in=SSA.name(*o_it, local_SSAt::LOOP_BACK, from);
    symbol_exprt out=SSA.read_rhs(*o_it, from);
  
    fixed_point.pre_state_vars.push_back(in);
    fixed_point.post_state_vars.push_back(out);
  }

  ssa_objectt guard=SSA.guard_symbol();
  fixed_point.pre_state_vars.push_back(SSA.name(guard, local_SSAt::LOOP_BACK, from));
  fixed_point.post_state_vars.push_back(SSA.name(guard, local_SSAt::OUT, from));
}

/*******************************************************************\

Function: ssa_fixed_pointt::do_backwards_edges

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_fixed_pointt::do_backwards_edges()
{
  // old program, if applicable
  if(use_old)
  {  
    forall_goto_program_instructions(i_it, SSA_old.goto_function.body)
    {
      if(i_it->is_backwards_goto())
        do_backwards_edge(SSA_old, i_it);
    }
  }

  // new program
  forall_goto_program_instructions(i_it, SSA_new.goto_function.body)
  {
    if(i_it->is_backwards_goto())
      do_backwards_edge(SSA_new, i_it);
  }
}

/*******************************************************************\

Function: ssa_fixed_pointt::compute_fixed_point

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_fixed_pointt::compute_fixed_point()
{
  do_backwards_edges();
  setup_properties();

  // set up transition relation
  
  // new function
  fixed_point.transition_relation << SSA_new;

  if(use_old)
  {
    // old function, if applicable
    fixed_point.transition_relation << SSA_old;
    
    // tie inputs together, if applicable
    tie_inputs_together(fixed_point.transition_relation);
  }
  
  // compute the fixed-point
  fixed_point();

  // we check the properties once we have the fixed point
  check_properties();
}

/*******************************************************************\

Function: ssa_fixed_pointt::check_properties

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_fixed_pointt::check_properties()
{
  for(propertiest::iterator
      p_it=properties.begin(); p_it!=properties.end(); p_it++)
  {
    solvert solver(ns);
    #if 0
    satcheckt satcheck;
    bv_pointerst solver(ns, satcheck);
    //solver.set_message_handler(get_message_handler());
    #endif

    // feed transition relation into solver
    solver << fixed_point.transition_relation;
    
    // feed in fixed-point
    solver << fixed_point.state_predicate;

    #ifdef DEBUG
    std::cout << "GUARD: " << from_expr(ns, "", p_it->guard) << "\n";
    std::cout << "CHECKING: " << from_expr(ns, "", p_it->condition) << "\n";
    #endif
    
    // feed in the assertion
    solver.set_to_true(p_it->guard);
    solver.set_to_false(p_it->condition);

    // now solve
    decision_proceduret::resultt result=solver.dec_solve();
   
    #ifdef DEBUG
    std::cout << "=======================\n";
    solver.print_assignment(std::cout);
    std::cout << "=======================\n";
    #endif

    tvt status;
    
    if(result==decision_proceduret::D_UNSATISFIABLE)
      status=tvt(true);
    else if(result==decision_proceduret::D_SATISFIABLE)
    {
      status=tvt(false);
      generate_countermodel(*p_it, solver);
    }
    else
      status=tvt::unknown();

    p_it->status=status;
    
    #ifdef DEBUG
    std::cout << "RESULT: " << status << "\n";
    std::cout << "\n";
    #endif
  }
}

/*******************************************************************\

Function: ssa_fixed_pointt::countermodel_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_fixed_pointt::countermodel_expr(
  const exprt &src,
  std::set<exprt> &dest)
{
  forall_operands(it, src)
    countermodel_expr(*it, dest);
  
  if(src.id()==ID_symbol)
    dest.insert(src);
}

/*******************************************************************\

Function: ssa_fixed_pointt::generate_countermodel

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_fixed_pointt::generate_countermodel(
  propertyt &property,
  const decision_proceduret &solver)
{
  // collect all expressions from SSA that seem interesting
  
  std::set<exprt> expressions;
  
  for(local_SSAt::nodest::const_iterator
      n_it=SSA_new.nodes.begin();
      n_it!=SSA_new.nodes.end();
      n_it++)
  {
    const local_SSAt::nodet &node=n_it->second;
    for(local_SSAt::nodet::equalitiest::const_iterator
        e_it=node.equalities.begin();
        e_it!=node.equalities.end();
        e_it++)
    {
      countermodel_expr(e_it->lhs(), expressions);
      countermodel_expr(e_it->rhs(), expressions);
    }

    for(local_SSAt::nodet::constraintst::const_iterator
        e_it=node.constraints.begin();
        e_it!=node.constraints.end();
        e_it++)
    {
      countermodel_expr(*e_it, expressions);
    }
  }
  
  if(use_old)
  {
    for(local_SSAt::nodest::const_iterator
        n_it=SSA_old.nodes.begin();
        n_it!=SSA_old.nodes.end();
        n_it++)
    {
      const local_SSAt::nodet &node=n_it->second;
      for(local_SSAt::nodet::equalitiest::const_iterator
          e_it=node.equalities.begin();
          e_it!=node.equalities.end();
          e_it++)
      {
        countermodel_expr(e_it->lhs(), expressions);
        countermodel_expr(e_it->rhs(), expressions);
      }

      for(local_SSAt::nodet::constraintst::const_iterator
          e_it=node.constraints.begin();
          e_it!=node.constraints.end();
          e_it++)
      {
        countermodel_expr(*e_it, expressions);
      }
    }
  }
  
  // now collect from property
  countermodel_expr(property.guard, expressions);
  countermodel_expr(property.condition, expressions);

  // get values for those expressions
  for(std::set<exprt>::const_iterator
      e_it=expressions.begin();
      e_it!=expressions.end();
      e_it++)
  {
    exprt value=solver.get(*e_it);
    if(value.is_not_nil())
      property.value_map[*e_it]=value;
  }
}

/*******************************************************************\

Function: ssa_fixed_pointt::setup_properties

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_fixed_pointt::setup_properties()
{
  forall_goto_program_instructions(i_it, SSA_new.goto_function.body)
  {
    if(i_it->is_assert())
    {
      properties.push_back(propertyt());
      properties.back().loc=i_it;
      properties.back().condition=SSA_new.read_rhs(i_it->guard, i_it);
      properties.back().guard=SSA_new.guard_symbol(i_it);
    }
  }
}
