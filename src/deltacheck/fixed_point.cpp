/*******************************************************************\

Module: Forward Greatest Fixed-Point

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#define DEBUG

#include "fixed_point.h"
#include "solver.h"

#ifdef DEBUG
#include <iostream>
#endif

/*******************************************************************\

Function: fixed_pointt::fixed_point

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void fixed_pointt::fixed_point()
{
  iteration_number=0;
  
  bool change;

  do
  {
    iteration_number++;
    
    #ifdef DEBUG
    std::cout << "Forward greatest fixed-point iteration #" << iteration_number << "\n";
    print(std::cout);
    #endif
   
    change=iteration();
  }
  while(change);

  #ifdef DEBUG
  std::cout << "Fixed-point after " << iteration_number
            << " iteration(s)\n";
  print(std::cout);
  #endif
}

/*******************************************************************\

Function: fixed_pointt::iteration

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool fixed_pointt::iteration()
{
  solvert solver(ns);

  // feed transition relation into solver
  for(constraintst::const_iterator
      it=transition_relation.begin();
      it!=transition_relation.end();
      it++)
    solver << *it;

  // feed current state predicate into solver
  state_predicate.set_to_true(solver);

  // solve
  solver.dec_solve();
 
  #ifdef DEBUG
  std::cout << "=======================\n";
  solver.print_assignment(std::cout);
  std::cout << "=======================\n";
  #endif

  // now get new post-state
  predicatet post_state;
  post_state.get(solver);

  // Now 'OR' with previous state predicate.
  // First rename post-state to pre-state.
  //post_state.rename(b_it->pre_predicate.guard, b_it->pre_predicate.vars);
    
  #if 0
  post_state.output(std::cout);
  #endif
    
  // make disjunction
  return state_predicate.disjunction(post_state);
}

/*******************************************************************\

Function: fixed_pointt::print

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void fixed_pointt::print(std::ostream &out) const
{
  /*
    out << "*** From " << be.from->location_number
        << " to " << be.to->location_number << "\n";

    out << "Pre: ";
    for(predicatet::var_listt::const_iterator
        v_it=be.pre_predicate.vars.begin();
        v_it!=be.pre_predicate.vars.end(); v_it++)
      out << " " << v_it->get_identifier();
    out << "\n";
    out << "GSym: " << be.pre_predicate.guard.get_identifier()
        << "\n";

    out << "Post:";
    for(predicatet::var_listt::const_iterator
        v_it=be.post_predicate.vars.begin();
        v_it!=be.post_predicate.vars.end(); v_it++)
      out << " " << v_it->get_identifier();
    out << "\n";
    out << "GSym: " << be.post_predicate.guard.get_identifier()
        << "\n";
    
    out << be.pre_predicate;

    out << "\n";
  }
  */
}
