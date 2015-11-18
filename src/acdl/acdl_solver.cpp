/*******************************************************************\

Module: ACDL Solver

Author: Rajdeep Mukherjee

\*******************************************************************/


#include <langapi/language_util.h>

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
     const exprt statement = worklist.back(); worklist.pop_back();
     //const exprt &rhs = l;
     std::cout<< "I am building heaven" << std::endl;
     std::cout<< "The expression is " << from_expr(SSA.ns, "", statement) << std::endl;

     // TODO: this is a workaround to handle booleans,
     //       must be implemented using a product domain
     if(statement.id()==ID_equal &&
	to_equal_expr(statement).lhs().type().id()==ID_bool)
     {
       std::vector<acdl_domaint::valuet> new_v;
       new_v.resize(1);
       new_v[0] = statement;
       domain.meet(new_v,v);
     }
     else
     {
       // compute update of abtract value
       acdl_domaint::varst vars;
       //TODO: select vars according to iteration strategy
       std::vector<acdl_domaint::valuet> new_v;
       new_v.resize(1);
       domain(statement,vars,v,new_v[0]);
       domain.meet(new_v,v);
     }

     // update worklist
     std::vector<acdl_domaint::statementt> predecs;
    
  }

  return property_checkert::UNKNOWN;
}
