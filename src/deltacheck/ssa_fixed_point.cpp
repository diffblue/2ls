/*******************************************************************\

Module: Data Flow Analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#define DEBUG

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

  if(function_SSA_old.goto_function.body.empty() ||
     function_SSA_new.goto_function.body.empty())
    return;
    
  // 1) parameters
  
  const code_typet::parameterst &p_new=
    function_SSA_new.goto_function.type.parameters();
    
  const code_typet::parameterst &p_old=
    function_SSA_old.goto_function.type.parameters();

  for(unsigned p=0; p<p_new.size(); p++)
    if(p<p_old.size() &&
       p_old[p].type()==p_new[p].type())
    {
      symbol_exprt s_old(p_old[p].get_identifier(), p_old[p].type());
      symbol_exprt s_new(p_new[p].get_identifier(), p_new[p].type());
      s_old=function_SSA_old.name_input(s_old);
      s_new=function_SSA_new.name_input(s_new);

      dest.push_back(equal_exprt(s_old, s_new));
    }
    
  // 2) globals
  
  for(function_SSAt::objectst::const_iterator
      it=function_SSA_new.objects.begin();
      it!=function_SSA_new.objects.end();
      it++)
  {
    const symbol_exprt &s=to_symbol_expr(*it);
    const symbolt &symbol=ns.lookup(s);
    if(!symbol.is_static_lifetime || !symbol.is_lvalue) continue;
    if(function_SSA_old.objects.find(s)==
       function_SSA_old.objects.end()) continue;
    
    symbol_exprt s_new=function_SSA_new.name_input(s);
    symbol_exprt s_old=function_SSA_old.name_input(s);

    dest.push_back(equal_exprt(s_old, s_new));
  }

  // 3) guard
  
  /*
  dest.set_to_true(
    equal_exprt(function_SSA_old.guard_symbol(l_old),
                function_SSA_new.guard_symbol(l_new)));
  */
}

/*******************************************************************\

Function: ssa_fixed_pointt::do_backwards_edge

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_fixed_pointt::do_backwards_edge(
  const function_SSAt &function_SSA,
  locationt from)
{
  assert(from->is_backwards_goto());
  
  //locationt to=from->get_target();

  // Record the objects modified by the loop to get
  // 'primed' (post-state) and 'unprimed' (pre-state) variables.
  for(function_SSAt::objectst::const_iterator
      o_it=function_SSA.objects.begin();
      o_it!=function_SSA.objects.end();
      o_it++)
  {
    symbol_exprt in=function_SSA.name(*o_it, function_SSAt::LOOP_BACK, from);
    symbol_exprt out=function_SSA.read_rhs(*o_it, from);
  
    fixed_point.pre_state_vars.push_back(in);
    fixed_point.post_state_vars.push_back(out);
  }

  symbol_exprt guard=function_SSA.guard_symbol();
  fixed_point.pre_state_vars.push_back(function_SSA.name(guard, function_SSAt::LOOP_BACK, from));
  fixed_point.post_state_vars.push_back(function_SSA.name(guard, function_SSAt::OUT, from));
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
    forall_goto_program_instructions(i_it, function_SSA_old.goto_function.body)
    {
      if(i_it->is_backwards_goto())
        do_backwards_edge(function_SSA_old, i_it);
    }
  }

  // new program
  forall_goto_program_instructions(i_it, function_SSA_new.goto_function.body)
  {
    if(i_it->is_backwards_goto())
      do_backwards_edge(function_SSA_new, i_it);
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
  fixed_point.transition_relation << function_SSA_new;

  if(use_old)
  {
    // old function, if applicable
    fixed_point.transition_relation << function_SSA_old;
    
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
  
  for(function_SSAt::nodest::const_iterator
      n_it=function_SSA_new.nodes.begin();
      n_it!=function_SSA_new.nodes.end();
      n_it++)
  {
    const function_SSAt::nodet &node=n_it->second;
    for(function_SSAt::nodet::equalitiest::const_iterator
        e_it=node.equalities.begin();
        e_it!=node.equalities.end();
        e_it++)
    {
      countermodel_expr(e_it->lhs(), expressions);
      countermodel_expr(e_it->rhs(), expressions);
    }

    for(function_SSAt::nodet::constraintst::const_iterator
        e_it=node.constraints.begin();
        e_it!=node.constraints.end();
        e_it++)
    {
      countermodel_expr(*e_it, expressions);
    }
  }
  
  if(use_old)
  {
    for(function_SSAt::nodest::const_iterator
        n_it=function_SSA_old.nodes.begin();
        n_it!=function_SSA_old.nodes.end();
        n_it++)
    {
      const function_SSAt::nodet &node=n_it->second;
      for(function_SSAt::nodet::equalitiest::const_iterator
          e_it=node.equalities.begin();
          e_it!=node.equalities.end();
          e_it++)
      {
        countermodel_expr(e_it->lhs(), expressions);
        countermodel_expr(e_it->rhs(), expressions);
      }

      for(function_SSAt::nodet::constraintst::const_iterator
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
  forall_goto_program_instructions(i_it, function_SSA_new.goto_function.body)
  {
    if(i_it->is_assert())
    {
      properties.push_back(propertyt());
      properties.back().loc=i_it;
      properties.back().condition=function_SSA_new.read_rhs(i_it->guard, i_it);
      properties.back().guard=function_SSA_new.guard_symbol(i_it);
    }
  }
}
