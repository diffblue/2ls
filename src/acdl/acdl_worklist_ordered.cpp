/*******************************************************************\

Module: ACDL Worklist Initialization (Based on node ordering)

Author: Rajdeep Mukherjee, Peter Schrammel

\*******************************************************************/

#include <util/find_symbols.h>
#include "acdl_worklist_ordered.h"
#define DEBUG


/*******************************************************************\

Function: acdl_worklist_orderedt::initialize()

  Inputs:

 Outputs:

 Purpose: Initialize the worklist

 \*******************************************************************/

void
acdl_worklist_orderedt::initialize (const local_SSAt &SSA)
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
       push_into_list(assert_worklist, *a_it);
       and_expr.push_back(*a_it);
       push_into_assertion_list(assert_list, not_exprt(*a_it));
       // push into worklist_vars
       acdl_domaint::varst avars;
       find_symbols(*a_it, avars);
       worklist_vars.insert(avars.begin(), avars.end());
    }
  }
  
  
  // Now compute the transitive dependencies
  //compute fixpoint mu X. assert_nodes u predecessor(X)
  while(!assert_worklist.empty() > 0) {
    // collect all the leaf nodes
    const acdl_domaint::statementt statement = pop_from_list(assert_worklist);

    // select vars in the present statement
    acdl_domaint::varst vars;
    select_vars (statement, vars);
    // compute the predecessors
    update(SSA, vars, predecs_worklist, statement);
    
    //std::list<acdl_domaint::statementt>::iterator 
    //  iterassert = std::find(assert_list.begin(), assert_list.end(), statement); 
    
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
        push(*it);
        push_into_assertion_list(assert_worklist, *it);
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
    if(it->id() == ID_equal) {
     exprt expr_rhs = to_equal_expr(*it).rhs();
     if(expr_rhs.id() == ID_constant || expr_rhs.is_true() || expr_rhs.is_false()) { 
       push_into_list(leaf_worklist, *it);
     }
     else if(expr_rhs.type().id() != ID_constant) { 
       push_into_list(inter_worklist, *it);
     }
    }
    else {
       push_into_list(inter_worklist, *it);
    }
  }

#if 0 
  // order the leaf nodes right after all assertions
  for(std::list<acdl_domaint::statementt>::const_iterator 
    it = worklist.begin(); it != worklist.end(); ++it) 
  {
    // Do we need to separately treat ID_constraint ?
    if(it->id() == ID_equal) {
     exprt expr_rhs = to_equal_expr(*it).rhs();
     if(expr_rhs.id() == ID_constant) 
       push_into_list(leaf_worklist, *it);
    // We do not push nondet elements in to the worklist
    /* std::string str("nondet");
     std::string rhs_str=id2string(expr_rhs.get(ID_identifier));
    std::size_t found = rhs_str.find(str); 
    // push the nondet statement in rhs
    if(found != std::string::npos)
      push_into_list(leaf_worklist, *it);
    */ 
     //exprt expr_rhs = expr.rhs();
     // select vars in the present statement
     acdl_domaint::varst vars_rhs;
     select_vars (expr_rhs, vars_rhs);

     for(std::list<acdl_domaint::statementt>::const_iterator it1 = worklist.begin(); it1 != worklist.end(); ++it1)
      {
        if(*it == *it1) continue;
        /*else {
         if(!(check_statement(*it1, vars_rhs))) {
           // *it is a leaf node
           //push_into_worklist(leaf_worklist, *it);
        }*/
         // this is an intermediate node, not leaf
         else {
           // pop the element from the list
           //const acdl_domaint::statementt statement = pop_from_worklist(worklist);
           push_into_list(inter_worklist, *it);
         }
      }
    }
  }
#endif    
    
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
  acdl_domaint::varst var_leaf;
  // insert leaf nodes
  while(!leaf_worklist.empty() > 0) {
    const acdl_domaint::statementt statement = pop_from_list(leaf_worklist);
    push_into_list (worklist, statement);
    acdl_domaint::varst lvars;
    find_symbols(statement, lvars);
    var_leaf.insert(lvars.begin(), lvars.end());
  }
    
  // insert intermediate nodes
  while(!inter_worklist.empty() > 0) {
    const acdl_domaint::statementt statement = pop_from_list(inter_worklist);
    push_into_list (worklist, statement);
    // push into worklist_vars
    acdl_domaint::varst avars;
    find_symbols(statement, avars);
    // do not insert any leaf variables
    for(acdl_domaint::varst::const_iterator it = avars.begin(); it != avars.end(); ++it) {
     if(var_leaf.find(*it) == var_leaf.end())
       worklist_vars.insert(*it);
    }
  }

#ifdef DEBUG    
   std::cout << "The content of the ordered worklist is as follows: " << std::endl;
    for(std::list<acdl_domaint::statementt>::const_iterator 
      it = worklist.begin(); it != worklist.end(); ++it)
	  std::cout << "Worklist Element::" << from_expr(SSA.ns, "", *it) << std::endl;
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
    push(worklist, not_exp);
  }
  else {
    and_exprt final_and;
    std::swap(final_and.operands(), and_expr);
    not_exprt not_exp(final_and);
#ifdef DEBUG    
    std::cout << "First push: " << not_exp.pretty() << std::endl;
#endif    
    push(worklist, not_exp);
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
  push(worklist, SSA.nodes.front ().equalities.front ());
  #ifdef DEBUG
  std::cout << "First push: " << from_expr (SSA.ns, "", SSA.nodes.front().equalities.front ()) << std::endl;
  #endif
#endif
}

/************************************************************\

Function: acdl_worklist_orderedt::dec_update()

  Inputs:

 Outputs:

 Purpose: Initialize the worklist after a decision is made

 \*******************************************************************/

void
acdl_worklist_orderedt::dec_update (const local_SSAt &SSA, const acdl_domaint::statementt &stmt)
{
  // **********************************************************************
  // Initialization Strategy: Guarantees top-down and bottom-up propagation 
  // Decision -- Top
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
  
  push_into_list(assert_worklist, stmt); 
  // Now compute the transitive dependencies
  //compute fixpoint mu X. assert_nodes u predecessor(X)
  while(!assert_worklist.empty() > 0) {
    // collect all the leaf nodes
    const acdl_domaint::statementt statement = pop_from_list(assert_worklist);

    // select vars in the present statement
    acdl_domaint::varst vars;
    select_vars (statement, vars);
    // compute the predecessors
    update(SSA, vars, predecs_worklist, statement);
    
    //std::list<acdl_domaint::statementt>::iterator 
    //  iterassert = std::find(assert_list.begin(), assert_list.end(), statement); 
    
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
        push(*it);
        push_into_assertion_list(assert_worklist, *it);
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
  
  // order the leaf nodes right after all assertions
  for(std::list<acdl_domaint::statementt>::const_iterator 
    it = worklist.begin(); it != worklist.end(); ++it) 
  {
    if(it->id() == ID_equal) {
     exprt expr_rhs = to_equal_expr(*it).rhs();
     if(expr_rhs.id() == ID_constant || expr_rhs.is_true() || expr_rhs.is_false()) { 
       push_into_list(leaf_worklist, *it);
     }
     else if(expr_rhs.type().id() != ID_constant) { 
       push_into_list(inter_worklist, *it);
     }
    }
    else {
       push_into_list(inter_worklist, *it);
    }
  }
  
  
 #if 0 
  
  for(std::list<acdl_domaint::statementt>::const_iterator 
    it = worklist.begin(); it != worklist.end(); ++it) 
  {
    if(it->id() == ID_equal) {
     exprt expr_rhs = to_equal_expr(*it).rhs();
     if(expr_rhs.type().id() == ID_constant) { 
       std::cout << "The type is " << expr_rhs.type().id() << std::endl;
       std::cout << "pushing equalities into leaf" << std::endl;   
       push_into_list(leaf_worklist, *it);
     }
     else if(expr_rhs.type().id() != ID_constant) { 
       std::cout << "pushing equalities into inter" << std::endl;   
       push_into_list(inter_worklist, *it);
     }
    }
    else {
       std::cout << "pushing constraint" << std::endl;   
       push_into_list(inter_worklist, *it);
    }
  }
#endif
    #if 0
    // Do we need to separately treat ID_constraint ?
    if(it->id() == ID_equal) {
     exprt expr_rhs = to_equal_expr(*it).rhs();
     if(expr_rhs.id() == ID_constant) 
       push_into_list(leaf_worklist, *it);
    // We do not push nondet elements in to the worklist
    /* std::string str("nondet");
     std::string rhs_str=id2string(expr_rhs.get(ID_identifier));
    std::size_t found = rhs_str.find(str); 
    // push the nondet statement in rhs
    if(found != std::string::npos)
      push_into_list(leaf_worklist, *it);
    */ 
     //exprt expr_rhs = expr.rhs();
     // select vars in the present statement
     acdl_domaint::varst vars_rhs;
     select_vars (expr_rhs, vars_rhs);

     for(std::list<acdl_domaint::statementt>::const_iterator it1 = worklist.begin(); it1 != worklist.end(); ++it1)
      {
        if(*it == *it1) continue;
        else {
         /*if(!(check_statement(*it1, vars_rhs))) {
           // *it is a leaf node
           //push_into_worklist(leaf_worklist, *it);
        }
         // this is an intermediate node, not leaf
         else {*/
           push_into_list(inter_worklist, *it);
        }
      }
    }
  }
  #endif

    
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
  // insert decisions as the first statement
  // worklist.push_back(stmt);

  acdl_domaint::varst dec_vars;
  // find all symbols in the decision expression
  find_symbols(stmt, dec_vars);
  live_variables.insert(dec_vars.begin(),dec_vars.end());
  // insert leaf nodes
  while(!leaf_worklist.empty() > 0) {
    const acdl_domaint::statementt statement = pop_from_list(leaf_worklist);
    push_into_list (worklist, statement);
    acdl_domaint::varst leaf_vars;
    std::set<exprt> lvars;
    
    // find all symbols in the leaf expression
    find_symbols(statement, leaf_vars);
    live_variables.insert(leaf_vars.begin(),leaf_vars.end());
  
    find_symbols(statement, lvars);
  }
    
  // insert intermediate nodes
  while(!inter_worklist.empty() > 0) {
    const acdl_domaint::statementt statement = pop_from_list(inter_worklist);
    push_into_list (worklist, statement);
    acdl_domaint::varst inter_vars;
    // find all symbols in the leaf expression
    find_symbols(statement, inter_vars);
    live_variables.insert(inter_vars.begin(),inter_vars.end());
  }
  
#ifdef DEBUG    
   std::cout << "The content of the ordered worklist is as follows: " << std::endl;
    for(std::list<acdl_domaint::statementt>::const_iterator 
      it = worklist.begin(); it != worklist.end(); ++it)
	  std::cout << "Worklist Element::" << from_expr(SSA.ns, "", *it) << std::endl;
#endif    
  
}



/*******************************************************************\

Function: acdl_worklist_baset::push_into_list()

  Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

void
acdl_worklist_orderedt::push_into_list (listt &lexpr,
				  const acdl_domaint::statementt &statement)
{
  for(listt::const_iterator it = lexpr.begin();
      it != lexpr.end(); ++it)
    if(statement == *it)
      return;
  lexpr.push_back(statement);
}

/*******************************************************************\

Function: acdl_worklist_baset::pop_from_list()

  Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

const acdl_domaint::statementt
acdl_worklist_orderedt::pop_from_list (listt &lexpr)
{
  const acdl_domaint::statementt statement = lexpr.front();
  lexpr.pop_front();
  return statement;
}


/*******************************************************************\

Function: acdl_worklist_orderedt::update()

  Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

void
acdl_worklist_orderedt::update (const local_SSAt &SSA,
                               const acdl_domaint::varst &vars,
                               
                               listt &lexpr, 
                               const acdl_domaint::statementt &current_statement)
{
   
  // dependency analysis loop for equalities
  for (local_SSAt::nodest::const_iterator n_it = SSA.nodes.begin ();
      n_it != SSA.nodes.end (); n_it++)
  {

    for (local_SSAt::nodet::equalitiest::const_iterator e_it =
        n_it->equalities.begin (); e_it != n_it->equalities.end (); e_it++)
    {
      exprt expr_rhs = to_equal_expr(*e_it).rhs();
      //if(expr_rhs.id() == ID_constant) {
      std::string str("nondet");
      expr_rhs = e_it->rhs();
      std::string rhs_str=id2string(expr_rhs.get(ID_identifier));
      std::size_t found = rhs_str.find(str); 
      // push the nondet statement in rhs
      if(found != std::string::npos) {
        std::cout << "Not inserting nondet elements " << std::endl; 
       continue; 
      }
      // the statement has already been processed, so no action needed
      if(*e_it == current_statement) continue;

      if (check_statement (*e_it, vars)) {
        push_into_list (lexpr, *e_it);
        #ifdef DEBUG
        std::cout << "Push: " << from_expr (SSA.ns, "", *e_it) << std::endl;
        #endif
      }
    }
    for (local_SSAt::nodet::constraintst::const_iterator c_it =
        n_it->constraints.begin (); c_it != n_it->constraints.end (); c_it++)
    {
      if(*c_it == current_statement) continue;
      if (check_statement (*c_it, vars)) {
        push_into_list (lexpr, *c_it);
        #ifdef DEBUG
        std::cout << "Push: " << from_expr (SSA.ns, "", *c_it) << std::endl;
        #endif
      }
    }
    for (local_SSAt::nodet::assertionst::const_iterator a_it =
        n_it->assertions.begin (); a_it != n_it->assertions.end (); a_it++)
    {
      // for now, store the decision variable as variables 
      // that appear only in properties
      // find all variables in an assert statement
      //assert_listt alist;
      //push_into_assertion_list(alist, *a_it);
      if(*a_it == current_statement) continue;
      if (check_statement (*a_it, vars)) {
        push_into_list (lexpr, not_exprt (*a_it));
        #ifdef DEBUG
        std::cout << "Push: " << from_expr (SSA.ns, "", not_exprt(*a_it)) << std::endl;
        #endif
      }
    }
  }
}

/*******************************************************************\

Function: acdl_worklist_orderedt::initialize()

  Inputs:

 Outputs:

 Purpose: Initialize the worklist

 \*******************************************************************/

void
acdl_worklist_orderedt::initialize_live_variables ()
{
//#if 0  
  //Strategy 1: initialize live variables by adding all vars
  for(std::list<acdl_domaint::statementt>::const_iterator 
      it = worklist.begin(); it != worklist.end(); ++it) {
    acdl_domaint::varst insert_vars;
    select_vars(*it, insert_vars);
    for(acdl_domaint::varst::const_iterator it1 = 
        insert_vars.begin(); it1 != insert_vars.end(); ++it1)
      live_variables.insert(*it1);   
  }
//#endif
/* 
  // Strategy 2: initialize live variables by inserting only lhs vars 
  // from ID_equal statements for forward analysis 
  for(std::list<acdl_domaint::statementt>::const_iterator 
      it = worklist.begin(); it != worklist.end(); ++it) {
    if(it->id() == ID_equal) {
      exprt expr_lhs = to_equal_expr(*it).lhs();
      find_symbols(expr_lhs, live_variables);
    }
  }

#if 0
  // Strategy 3: initialize live variables by inserting only rhs vars 
  // from ID_equal statements for backward analysis 
  for(std::list<acdl_domaint::statementt>::const_iterator 
      it = worklist.begin(); it != worklist.end(); ++it) {
    if(it->id() == ID_equal) {
      exprt expr_rhs = to_equal_expr(*it).rhs();
      find_symbols(expr_rhs, live_variables);
    }
  }
#endif
*/

#ifdef DEBUG
  std::cout << "Printing all live variables" << std::endl;
  for(acdl_domaint::varst::const_iterator 
    it = live_variables.begin(); it != live_variables.end(); ++it)
      std::cout << it->get_identifier() << "," << std::endl;
#endif
}   

