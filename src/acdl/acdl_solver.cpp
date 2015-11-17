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

 In ACDCL, the first element in the worklist is an assertion
\*******************************************************************/

property_checkert::resultt acdl_solvert::operator()(const local_SSAt &SSA)
{
  unsigned iteration_number=0;
  bool change;
  std::list<acdl_domaint::statementt> worklist;
  acdl_domaint::valuet v = true_exprt();
  
  std::vector<equal_exprt> first_statement;
  exprt expression;
  for(local_SSAt::nodest::const_iterator n_it = SSA.nodes.begin();
      n_it != SSA.nodes.end(); n_it++) {
    for(local_SSAt::nodet::equalitiest::const_iterator f_it =
	 	  n_it->equalities.begin(); f_it != n_it->equalities.end(); f_it++) {
       expression = *f_it;
       //assert(f_it->.id()==ID_equal);
	   first_statement.push_back(*f_it);
       // Now insert the first statement into the worklist
       worklist.push_back(expression);
    }
  }
  while(worklist.size() > 0)
  {
     const exprt l = worklist.back(); worklist.pop_back();
     //const exprt &rhs = l;
     std::cout<< "I am building heaven" << std::endl;
     std::cout<< "The expression is " << l << std::endl;
     std::vector<acdl_domaint::statementt> predecs;
  }
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
