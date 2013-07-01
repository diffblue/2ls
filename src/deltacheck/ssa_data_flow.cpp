/*******************************************************************\

Module: Data Flow Analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#define DEBUG

#include <util/decision_procedure.h>

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
    exprt in=function_SSA.name(*o_it, function_SSAt::IN, result.to);
    exprt out=function_SSA.name(*o_it, function_SSAt::OUT, result.from);
  
    result.in_vars.push_back(in);
    result.out_vars.push_back(out);
  }

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

  initialize_invariant();
  iteration_number=0;
  
  bool change;

  do
  {
    iteration_number++;
    
    #ifdef DEBUG
    std::cout << "Iteration #" << iteration_number << std::endl;
    print_invariant(std::cout);
    #endif
  
    change=iteration();
  }
  while(change);
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

  // feed in current predicates
  for(backwards_edgest::const_iterator
      b_it=backwards_edges.begin();
      b_it!=backwards_edges.end();
      b_it++)
    solver.assume(b_it->in_vars, b_it->predicate);
  
  // solve
  solver.dec_solve();

  // now weaken predicates
  for(backwards_edgest::iterator
      b_it=backwards_edges.begin();
      b_it!=backwards_edges.end();
      b_it++)
    solver.weaken(b_it->out_vars, b_it->predicate);
  
  return false;
}

/*******************************************************************\

Function: ssa_data_flowt::initialize_invariant

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_data_flowt::initialize_invariant()
{
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
        << " to " << be.to->location_number << std::endl;

    out << "In: ";
    for(solvert::var_sett::const_iterator
        v_it=be.in_vars.begin(); v_it!=be.in_vars.end(); v_it++)
      out << " " << *v_it;
    out << std::endl;

    out << "Out:";
    for(solvert::var_sett::const_iterator
        v_it=be.out_vars.begin(); v_it!=be.out_vars.end(); v_it++)
      out << " " << *v_it;
    out << std::endl;
    
    out << be.predicate;

    out << std::endl;
  }
}
