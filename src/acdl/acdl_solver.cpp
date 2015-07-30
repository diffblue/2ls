/*******************************************************************\

Module: ACDL Solver

Author: Rajdeep Mukherjee

\*******************************************************************/



#include "acdl_solver.h"
#include "acdl_domain.h"

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
  typedef std::list<acdl_domaint::statementt> worklist;
  acdl_domaint::valuet v = true_exprt();
  
  typedef std::vector<equal_exprt> first_statement;  
  
  //for(local_SSAt::nodest::const_iterator n_it = SSA.nodes.begin(); 
  //    n_it != SSA.nodes.end(); n_it++)
    
  // wrong attempt: first_statement.push_back(n_it->equalities);
  // Now each node can have multiple equalities all of which 
  // needs to be inserted 
  //first_statement = SSA.nodes.begin()->equalities;
  
  // Now insert the first statement into the worklist
  //worklist.push_back(SSA.nodes.begin()->equalities);
  do
  {
    iteration_number++;
    
    #ifdef DEBUG
    std::cout << "\n"
              << "******** Iteration #"
              << iteration_number << std::endl;
    #endif
   
    // do it

    
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
