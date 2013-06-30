/*******************************************************************\

Module: Data Flow Analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#define DEBUG

#include "ssa_data_flow.h"
#include "solver.h"

#ifdef DEBUG
#include <iostream>
#endif

/*******************************************************************\

Function: ssa_data_flowt::fixed_point

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_data_flowt::fixed_point()
{
  initialize_invariant();
  iteration_number=0;

  do
  {
    iteration_number++;
    
    #ifdef DEBUG
    std::cout << "Iteration #" << iteration_number << std::endl;
    print_invariant(std::cout);
    #endif
  
    change=false;
    iteration();
  }
  while(change);
}

/*******************************************************************\

Function: ssa_data_flowt::iteration

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_data_flowt::iteration()
{
  solvert solver(function_SSA.ns);

  
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

