/*******************************************************************\

Module: Data Flow Analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#define DEBUG

#include <util/decision_procedure.h>
#include <util/simplify_expr.h>

#include "ssa_data_flow.h"
#include "solver.h"

#ifdef DEBUG
#include <iostream>
#endif

/*******************************************************************\

Function: ssa_data_flowt::get_backwards_edge

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

ssa_data_flowt::backwards_edget ssa_data_flowt::backwards_edge(locationt from)
{
  assert(from->is_backwards_goto());

  backwards_edget result;

  result.from=from;
  result.to=from->get_target();

  for(function_SSAt::objectst::const_iterator
      o_it=function_SSA.objects.begin();
      o_it!=function_SSA.objects.end();
      o_it++)
  {
    symbol_exprt in=function_SSA.read_in(*o_it, result.to);
    symbol_exprt out=function_SSA.read(*o_it, result.from);
  
    result.pre_predicate.vars.push_back(in);
    result.post_predicate.vars.push_back(out);
  }

  symbol_exprt guard=function_SSA.guard_symbol();
  result.pre_predicate.guard=function_SSA.name(guard, function_SSAt::LOOP, result.to);
  result.post_predicate.guard=function_SSA.name(guard, function_SSAt::OUT, result.from);

  // Initially, we start with the strongest invariant: false
  // This gets weakened incrementally.
  result.pre_predicate.make_false();

  return result;  
}

/*******************************************************************\

Function: ssa_data_flowt::get_backwards_edges

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_data_flowt::get_backwards_edges()
{
  forall_goto_program_instructions(i_it, function_SSA.goto_function.body)
  {
    if(i_it->is_backwards_goto())
      backwards_edges.push_back(backwards_edge(i_it));
  }
}

/*******************************************************************\

Function: ssa_data_flowt::fixed_point

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_data_flowt::fixed_point()
{
  get_backwards_edges();
  setup_properties();

  iteration_number=0;
  
  bool change;

  do
  {
    iteration_number++;
    
    #ifdef DEBUG
    std::cout << "Iteration #" << iteration_number << "\n";
    print_invariant(std::cout);
    #endif
   
    change=iteration();
  }
  while(change);

  // we check the properties once we have the fixed point
  check_properties();
}

/*******************************************************************\

Function: ssa_data_flowt::iteration

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool ssa_data_flowt::iteration()
{
  solvert solver(function_SSA.ns);

  // feed SSA into solver
  solver << function_SSA;

  // feed in current pre-state predicates
  for(backwards_edgest::const_iterator
      b_it=backwards_edges.begin();
      b_it!=backwards_edges.end();
      b_it++)
    b_it->pre_predicate.set_to_true(solver);
  
  // feed in assertions to aid fixed-point computation
  for(propertiest::const_iterator
      p_it=properties.begin(); p_it!=properties.end(); p_it++)
  {
    #ifdef DEBUG
    std::cout << "ASSERTION: " << from_expr(p_it->condition) << std::endl;
    #endif
    solver.add_expression(p_it->condition);
  }

  // solve
  solver.dec_solve();
 
  #ifdef DEBUG
  std::cout << "=======================\n";
  solver.print_assignment(std::cout);
  std::cout << "=======================\n";
  #endif

  // now get new value of post-state predicates
  for(backwards_edgest::iterator
      b_it=backwards_edges.begin();
      b_it!=backwards_edges.end();
      b_it++)
    b_it->post_predicate.get(solver);

  // now 'OR' with previous pre-state predicates

  bool change=false;

  for(backwards_edgest::iterator
      b_it=backwards_edges.begin();
      b_it!=backwards_edges.end();
      b_it++)
  {
    // copy
    predicatet tmp=b_it->post_predicate;
    
    // rename
    tmp.rename(b_it->pre_predicate.guard, b_it->pre_predicate.vars);
    
    #if 0
    tmp.output(std::cout);
    #endif
    
    // make disjunction
    if(b_it->pre_predicate.disjunction(tmp))
      change=true;
  }
  
  return change;
}

/*******************************************************************\

Function: ssa_data_flowt::check_properties

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_data_flowt::check_properties()
{
  for(propertiest::iterator
      p_it=properties.begin(); p_it!=properties.end(); p_it++)
  {
    solvert solver(function_SSA.ns);

    // feed SSA into solver
    solver << function_SSA;

    // feed in current fixed-point
    for(backwards_edgest::const_iterator
        b_it=backwards_edges.begin();
        b_it!=backwards_edges.end();
        b_it++)
      b_it->pre_predicate.set_to_true(solver);

    #ifdef DEBUG
    std::cout << "GUARD: " << from_expr(function_SSA.ns, "", p_it->guard) << "\n";
    std::cout << "CHECKING: " << from_expr(function_SSA.ns, "", p_it->condition) << "\n";
    #endif
    
    // feed in the assertion
    solver.set_to_true(p_it->guard);
    solver.add_expression(p_it->condition);

    // solve
    solver.dec_solve();
   
    #ifdef DEBUG
    std::cout << "=======================\n";
    solver.print_assignment(std::cout);
    std::cout << "=======================\n";
    #endif

    exprt g=solver.get(p_it->condition);
    simplify(g, function_SSA.ns);

    #ifdef DEBUG
    std::cout << "RESULT: " << from_expr(function_SSA.ns, "", g) << "\n";
    std::cout << "\n";
    #endif

    tvt status;
    
    if(g.is_true())
      status=tvt(true);
    else if(g.is_false())
      status=tvt(false);
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

Function: ssa_data_flowt::setup_properties

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_data_flowt::setup_properties()
{
  forall_goto_program_instructions(i_it, function_SSA.goto_function.body)
  {
    if(i_it->is_assert())
    {
      properties.push_back(propertyt());
      properties.back().loc=i_it;
      properties.back().condition=function_SSA.read(i_it->guard, i_it);
      properties.back().guard=function_SSA.guard_symbol(i_it);
    }
  }
}

/*******************************************************************\

Function: ssa_data_flowt::print_invariant

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_data_flowt::print_invariant(std::ostream &out) const
{
  for(backwards_edgest::const_iterator
      b_it=backwards_edges.begin();
      b_it!=backwards_edges.end();
      b_it++)
  {
    const backwards_edget &be=*b_it;
  
    out << "*** From " << be.from->location_number
        << " to " << be.to->location_number << "\n";

    out << "Pre: ";
    for(predicatet::var_listt::const_iterator
        v_it=be.pre_predicate.vars.begin(); v_it!=be.pre_predicate.vars.end(); v_it++)
      out << " " << v_it->get_identifier();
    out << "\n";
    out << "GSym: " << be.pre_predicate.guard.get_identifier()
        << "\n";

    out << "Post:";
    for(predicatet::var_listt::const_iterator
        v_it=be.post_predicate.vars.begin(); v_it!=be.post_predicate.vars.end(); v_it++)
      out << " " << v_it->get_identifier();
    out << "\n";
    out << "GSym: " << be.post_predicate.guard.get_identifier()
        << "\n";
    
    out << be.pre_predicate;

    out << "\n";
  }
}
