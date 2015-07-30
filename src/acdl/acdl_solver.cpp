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

 Purpose: Worklist algorithm sketch 
 list<statementt> worklist;
 valuet v = true_exprt();
 // Initialize worklist
 // wl <-- first_statement in localSSA.nodes;
 do {
  s = worklist_pop();
  post(s,v); // this will update v
  // Find statements where s.lhs appears in RHS of SSA nodes, insert the whole statement in worklist
  // To do this, iterate over the localSSA.nodes and collect all these statements
   populate_worklist(s.lhs); 
 } while(worklist != 0);

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
