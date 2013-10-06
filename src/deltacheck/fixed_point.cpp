/*******************************************************************\

Module: Forward Least Fixed-Point

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#define DEBUG

#include "fixed_point.h"
#include "solver.h"

#ifdef DEBUG
#include <iostream>
#endif

/*******************************************************************\

Function: fixed_pointt::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void fixed_pointt::operator()()
{
  iteration_number=0;
  
  // Set up the state predicate, starting with 'false'
  // (the empty set).

  state_predicate.state_vars=pre_state_vars;
  state_predicate.make_false();
  
  bool change;

  do
  {
    iteration_number++;
    
    #ifdef DEBUG
    std::cout << "\n"
              << "******** Forward least fixed-point iteration #"
              << iteration_number << "\n";
    #endif
   
    change=iteration();
  }
  while(change);

  #ifdef DEBUG
  std::cout << "Fixed-point after " << iteration_number
            << " iteration(s)\n";
  output(std::cout);
  #endif
}

/*******************************************************************\

Function: fixed_pointt::iteration

  Inputs:

 Outputs: 'true' if there is a change in the state predicate

 Purpose:

\*******************************************************************/

bool fixed_pointt::iteration()
{
  solvert solver(ns);

  // Feed transition relation into solver.
  for(constraintst::const_iterator
      it=transition_relation.begin();
      it!=transition_relation.end();
      it++)
    solver << *it;

  // Feed current state predicate into solver.
  state_predicate.set_to_true(solver);
  
  #ifdef DEBUG
  std::cout << "Entry state:\n";
  output(std::cout);
  #endif

  // solve
  solver.dec_solve();
 
  #ifdef DEBUG
  std::cout << "=======================\n";
  solver.print_assignment(std::cout);
  std::cout << "=======================\n";
  #endif

  // now get new post-state
  predicatet post_state;
  post_state.state_vars=post_state_vars;
  
  post_state.get(solver);

  // Now 'OR' with previous state predicate.
  // First rename post-state to pre-state.
  post_state.rename(pre_state_vars);
    
  #ifdef DEBUG
  std::cout << "Post state:\n";
  post_state.output(std::cout);
  #endif
    
  // Form disjunction of previous state predicate and the new one.
  return state_predicate.disjunction(post_state);
}

/*******************************************************************\

Function: fixed_pointt::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void fixed_pointt::output(std::ostream &out) const
{
  state_predicate.output(out);
}
