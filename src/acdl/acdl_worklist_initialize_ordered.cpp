/*******************************************************************\

Module: ACDL Worklist Initialization (Based on node ordering)

Author: Rajdeep Mukherjee, Peter Schrammel

\*******************************************************************/

#include "acdl_worklist_initialize_ordered.h"

/*******************************************************************\

Function: acdl_worklist_initialize_orderedt::operator()

  Inputs:

 Outputs:

 Purpose: Initialize the worklist

 \*******************************************************************/

void
acdl_worklist_initialize_orderedt::operator() (const local_SSAt &SSA, worklistt &worklist)
{
  
  // **********************************************************************
  // Initialization Strategy: Guarantees top-down and bottom-up propagation 
  // Assertions -- Top
  // Leaf node  -- Middle
  // Rest       -- Bottom
  // **********************************************************************
  typedef std::list<acdl_domaint::statementt> assert_worklistt;
  assert_worklistt assert_worklist; 
  typedef std::list<acdl_domaint::statementt> predecs_worklistt;
  predecs_worklistt predecs_worklist; 
  typedef std::list<acdl_domaint::statementt> leaf_worklistt;
  leaf_worklistt leaf_worklist; 
  typedef std::list<acdl_domaint::statementt> inter_worklistt;
  inter_worklistt inter_worklist; 
  assert_listt assert_list;
  if (SSA.nodes.empty ())
    return;
  // insert the assertions like (!(a1 && a2 && a3)) on to the worklist
  and_exprt::operandst and_expr;
  for (local_SSAt::nodest::const_iterator n_it = SSA.nodes.begin ();
      n_it != SSA.nodes.end (); n_it++)
  {
    for (local_SSAt::nodet::assertionst::const_iterator a_it =
        n_it->assertions.begin (); a_it != n_it->assertions.end (); a_it++)
    {
       push_into_worklist(assert_worklist, *a_it);
       and_expr.push_back(*a_it);
       push_into_assertion_list(assert_list, not_exprt(*a_it));

    }
  }
  
  
  // Now compute the transitive dependencies
  //compute fixpoint mu X. assert_nodes u predecessor(X)
  while(!assert_worklist.empty() > 0) {
    // collect all the leaf nodes
    const acdl_domaint::statementt statement = pop_from_worklist(assert_worklist);

    // select vars in the present statement
    acdl_domaint::varst vars;
    select_vars (statement, vars);
    // compute the predecessors
    update_worklist(SSA, vars, predecs_worklist, statement);
    
    std::list<acdl_domaint::statementt>::iterator 
      iterassert = std::find(assert_list.begin(), assert_list.end(), statement); 
    for(std::list<acdl_domaint::statementt>::const_iterator 
      it = predecs_worklist.begin(); it != predecs_worklist.end(); ++it) {
      std::list<acdl_domaint::statementt>::iterator finditer = 
                  std::find(worklist.begin(), worklist.end(), *it); 
    
      // This is required to prevent inserting 
      // individual assertions to the worklist       
      std::list<acdl_domaint::statementt>::iterator iterassert = 
        std::find(assert_list.begin(), assert_list.end(), *it); 
      if(finditer == worklist.end() && iterassert == assert_list.end())
      {
        // never seen this statement before
        push_into_worklist(worklist, *it);
        push_into_worklist(assert_worklist, *it);
      }
    }
  }
#ifdef DEBUG    
   std::cout << "The content of the sliced but unordered worklist is as follows: " << std::endl;
    for(std::list<acdl_domaint::statementt>::const_iterator it = worklist.begin(); it != worklist.end(); ++it) {
	  std::cout << "Sliced Unordered Worklist Element::" << from_expr(SSA.ns, "", *it) << std::endl;
    }
#endif    
  
  // order the leaf nodes right after all assertions
  for(std::list<acdl_domaint::statementt>::const_iterator 
    it = worklist.begin(); it != worklist.end(); ++it) 
  {
    // Do we need to separately treat ID_constraint ?
    if(it->id() == ID_equal) {
     exprt expr_rhs = to_equal_expr(*it).rhs();
     if(expr_rhs.id() == ID_constant) 
       push_into_worklist(leaf_worklist, *it);
     std::string str("nondet");
     std::string rhs_str=id2string(expr_rhs.get(ID_identifier));
    std::size_t found = rhs_str.find(str); 
    // push the nondet statement in rhs
    if(found != std::string::npos)
      push_into_worklist(leaf_worklist, *it);
     
     //exprt expr_rhs = expr.rhs();
     // select vars in the present statement
     acdl_domaint::varst vars_rhs;
     select_vars (expr_rhs, vars_rhs);

     for(std::list<acdl_domaint::statementt>::const_iterator it1 = worklist.begin(); it1 != worklist.end(); ++it1)
      {
        if(*it == *it1) continue;
        else {
         if(!(check_statement(*it1, vars_rhs))) {
           // *it is a leaf node
           //push_into_worklist(leaf_worklist, *it);
         }
         // this is an intermediate node, not leaf
         else {
           // pop the element from the list
           //const acdl_domaint::statementt statement = pop_from_worklist(worklist);
           push_into_worklist(inter_worklist, *it);
         }
        }
      }
    }
  }
#ifdef DEBUG
    for(std::list<acdl_domaint::statementt>::const_iterator it = leaf_worklist.begin(); it != leaf_worklist.end(); ++it) {
	  std::cout << "Leaf Element::" << from_expr(SSA.ns, "", *it) << std::endl;
    }
    for(std::list<acdl_domaint::statementt>::const_iterator it = inter_worklist.begin(); it != inter_worklist.end(); ++it) {
	  std::cout << "Intermediate Worklist Element::" << from_expr(SSA.ns, "", *it) << std::endl;
    }
#endif    
  // Now prepare the final worklist
  // empty the worklist
  /*while(!worklist.empty() > 0)
    const acdl_domaint::statementt statement = pop_from_worklist(assert_worklist);
  */
  worklist.clear();
  // insert assertions
  // Push the negation of the assertions into the worklist
  unsigned int size = and_expr.size();
	exprt::operandst::const_iterator it = and_expr.begin();
  if(size == 1) {
	  exprt::operandst::const_iterator it = and_expr.begin();
#ifdef DEBUG    
	  std::cout << "First single assertion push: " << *it << std::endl;
#endif    
	  exprt exp = *it;
	  // push this into worklist at the end as TOP element
    not_exprt not_exp(exp);
    worklist.push_back(not_exp);
  }
  else {
    and_exprt final_and;
    std::swap(final_and.operands(), and_expr);
    not_exprt not_exp(final_and);
#ifdef DEBUG    
    // push this into worklist at the end as TOP element
    std::cout << "First push: " << not_exp.pretty() << std::endl;
#endif    
    worklist.push_back(not_exp);
  }
  
  // insert leaf nodes
  while(!leaf_worklist.empty() > 0) {
    const acdl_domaint::statementt statement = pop_from_worklist(leaf_worklist);
    push_into_worklist(worklist, statement);
  }
  
  // insert intermediate nodes
  while(!inter_worklist.empty() > 0) {
    const acdl_domaint::statementt statement = pop_from_worklist(inter_worklist);
    push_into_worklist(worklist, statement);
  }
    
#ifdef DEBUG    
   std::cout << "The content of the ordered worklist is as follows: " << std::endl;
    for(std::list<acdl_domaint::statementt>::const_iterator it = worklist.begin(); it != worklist.end(); ++it) {
	  std::cout << "Worklist Element::" << from_expr(SSA.ns, "", *it) << std::endl;
    }
#endif    
   


#if 0
  // **********************************************
  // Initialization Strategy: Add only assertions
  // **********************************************
  if (SSA.nodes.empty ())
    return;
  
  // insert the assertions like (!(a1 && a2 && a3)) on to the worklist
  and_exprt::operandst and_expr;
  for (local_SSAt::nodest::const_iterator n_it = SSA.nodes.begin ();
      n_it != SSA.nodes.end (); n_it++)
  {
    for (local_SSAt::nodet::assertionst::const_iterator a_it =
        n_it->assertions.begin (); a_it != n_it->assertions.end (); a_it++)
    {
       and_expr.push_back(*a_it);
    }
  }
  unsigned int size = and_expr.size();
#ifdef DEBUG    
  std::cout << "The number of Assertions are : " << size << std::endl;
#endif  
	exprt::operandst::const_iterator it = and_expr.begin();
	std::cout << "First single assertion push: " << *it << std::endl;
  if(size == 1) {
	  exprt::operandst::const_iterator it = and_expr.begin();
#ifdef DEBUG    
	  std::cout << "First single assertion push: " << *it << std::endl;
#endif    
	  exprt exp = *it;
	  not_exprt not_exp(exp);
    push_into_worklist(worklist, not_exp);
  }
  else {
    and_exprt final_and;
    std::swap(final_and.operands(), and_expr);
    not_exprt not_exp(final_and);
#ifdef DEBUG    
    std::cout << "First push: " << not_exp.pretty() << std::endl;
#endif    
    push_into_worklist(worklist, not_exp);
  }
#endif

#if 0
  // **************************************************
  // Initialization Strategy: Add the first SSA element
  // **************************************************

  // check for equalities or constraints or next node
  if (SSA.nodes.empty ())
    return;
  assert(!SSA.nodes.front ().equalities.empty ());
  // insert the first SSA element on to the worklist
  push_into_worklist(worklist, SSA.nodes.front ().equalities.front ());
  #ifdef DEBUG
  std::cout << "First push: " << from_expr (SSA.ns, "", SSA.nodes.front().equalities.front ()) << std::endl;
  #endif
#endif
}

