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

 In ACDCL, we do gfp computation, so we start with TOP and perform
 forward abstract analysis to compute the post-condition of a statement
\************************************************************************/

property_checkert::resultt acdl_solvert::operator()(const local_SSAt &SSA)
{
  unsigned iteration_number=0;
  bool change;
  std::list<acdl_domaint::statementt> equalities_expr;
  std::list<acdl_domaint::statementt> constraints_expr;
  std::list<acdl_domaint::statementt> assertions_expr;
  std::list<acdl_domaint::statementt> worklist;
  acdl_domaint::valuet v = true_exprt();
  
  std::vector<equal_exprt> first_statement;
  local_SSAt::nodest::const_iterator it = SSA.nodes.begin();
  local_SSAt::nodet::equalitiest::const_iterator first = it->equalities.begin();
  exprt expression = *first;

  // insert the first element on to the worklist
  worklist.push_back(expression);
  
  // collect all equalities, constraints and assertions
  for(local_SSAt::nodest::const_iterator n_it = SSA.nodes.begin();
      n_it != SSA.nodes.end(); n_it++) {
    for(local_SSAt::nodet::equalitiest::const_iterator e_it =
	 	  n_it->equalities.begin(); e_it != n_it->equalities.end(); e_it++) {
       expression = *e_it;
       assert(e_it->id()==ID_equal);
       //std::cout<< "The expression is " << e_it->pretty() << std::endl;
       equalities_expr.push_back(expression);
    }
    for(local_SSAt::nodet::assertionst::const_iterator a_it =
    	  n_it->assertions.begin(); a_it != n_it->assertions.end(); a_it++) {
         expression = *a_it;
         assert(a_it->id()==ID_assert);
         assertions_expr.push_back(expression);
    }
    
    for(local_SSAt::nodet::constraintst::const_iterator c_it =
    	  n_it->constraints.begin(); c_it != n_it->constraints.end(); c_it++) {
         expression = *c_it;
         constraints_expr.push_back(expression);
    }
  }

  while(worklist.size() > 0)
  {
     const exprt statement = worklist.back();
     worklist.pop_back();
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
       // v will get the new value of new_v
       domain.meet(new_v,v);
     }
     else
     {
       //TODO: select vars according to iteration strategy
       // compute update of abstract value
       acdl_domaint::varst vars;
       std::vector<acdl_domaint::valuet> new_v;
       new_v.resize(1);
       domain(statement,vars,v,new_v[0]);
       // meet is computed because we are doing gfp
       domain.meet(new_v,v);
     }
     exprt lhs_var;
     if(statement.id()==ID_equal)
       lhs_var = to_equal_expr(statement).lhs();

     // dependency analysis loop for equalities
     for(local_SSAt::nodest::const_iterator n_it = SSA.nodes.begin();
           n_it != SSA.nodes.end(); n_it++) {
         for(local_SSAt::nodet::equalitiest::const_iterator e_it =
     	 	  n_it->equalities.begin(); e_it != n_it->equalities.end(); e_it++) {
            expression = *e_it;
            assert(e_it->id()==ID_equal);
            exprt& rhs_var = to_equal_expr(expression).rhs();
            //check if the lhs_var matches any rhs_var of equalities statement
            if(rhs_var == lhs_var)
              // update worklist after computing dependency analysis
              worklist.push_back(expression);
         }
     }

     std::vector<acdl_domaint::statementt> predecs;
   }

  return property_checkert::UNKNOWN;
}
