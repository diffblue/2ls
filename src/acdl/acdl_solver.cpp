/*******************************************************************\

Module: ACDL Solver

Author: Rajdeep Mukherjee

\*******************************************************************/



#include "acdl_solver.h"

#ifdef DEBUG
#include <iostream>
#endif

/*******************************************************************\

Function: acdl_solvert::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

property_checkert::resultt acdl_solvert::operator()(const local_SSAt &SSA)
{
  unsigned iteration_number=0;
  bool change;

  do
  {
    iteration_number++;
    
    #ifdef DEBUG
    std::cout << "\n"
              << "******** Iteration #"
              << iteration_number << std::endl;
    #endif
   
    // DO STUFF
    change = false;

    if(change) 
    {

      #ifdef DEBUG
      std::cout << "Value after " << iteration_number
		<< " iteration(s):" << std::endl;
//      domain->output_value(std::cout,*result,SSA.ns);
      #endif
    }
  }
  while(change);

  return property_checkert::UNKNOWN;
}
