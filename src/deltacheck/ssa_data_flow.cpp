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

ssa_data_flowt::backwards_edget ssa_data_flowt::backwards_edge(locationt loc)
{
  assert(loc->is_backwards_goto());

  backwards_edget result;

  result.loc=loc;
  //result.in_vars=
  //result.out_vars=
  
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
}
