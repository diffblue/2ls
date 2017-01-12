/*******************************************************************\

Module: ACDL Worklist Initialization (Based on node ordering)

Author: Rajdeep Mukherjee, Peter Schrammel

\*******************************************************************/

#include <algorithm>

#include <util/find_symbols.h>
#include "acdl_worklist_ordered.h"
// #define DEBUG


/*******************************************************************\

  Function: acdl_worklist_orderedt::initialize()

  Inputs:

  Outputs:

  Purpose: Initialize the worklist

\*******************************************************************/

void
acdl_worklist_orderedt::initialize (const local_SSAt &SSA, const exprt &assertion, const exprt& additional_constraint)
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

  #if 0
  if (SSA.nodes.empty ())
    return;
  #endif
  if(statements.empty()) return;

  // insert the assertions like (!(a1 && a2 && a3)) on to the worklist
  #if 0
  and_exprt::operandst and_expr;
  for (local_SSAt::nodest::const_iterator n_it=SSA.nodes.begin ();
      n_it!=SSA.nodes.end (); n_it++)
  {
    for (local_SSAt::nodet::assertionst::const_iterator a_it=
        n_it->assertions.begin (); a_it!=n_it->assertions.end (); a_it++)
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
  #endif
  push_into_list(assert_worklist, assertion);
  push_into_assertion_list(assert_list, not_exprt(assertion));
  acdl_domaint::varst avars;
  find_symbols(assertion, avars);
  worklist_vars.insert(avars.begin(), avars.end());

  // Now compute the transitive dependencies
  // compute fixpoint mu X. assert_nodes u predecessor(X)
  while(!assert_worklist.empty() > 0) {
#ifdef DEBUG
    std::cout << "Populating the worklist" << std::endl;
#endif
    // collect all the leaf nodes
    const acdl_domaint::statementt statement=pop_from_list(assert_worklist);

    // select vars in the present statement
    acdl_domaint::varst vars;
    select_vars (statement, vars);
    // compute the predecessors
    update(SSA, vars, predecs_worklist, statement, assertion);

    // std::list<acdl_domaint::statementt>::iterator
    //  iterassert=std::find(assert_list.begin(), assert_list.end(), statement);

    for(std::list<acdl_domaint::statementt>::const_iterator
      it=predecs_worklist.begin(); it!=predecs_worklist.end(); ++it) {
      std::list<acdl_domaint::statementt>::iterator finditer=
                  std::find(worklist.begin(), worklist.end(), *it);

      // This is required to prevent inserting
      // individual assertions to the worklist
      std::list<acdl_domaint::statementt>::iterator iterassert=
        std::find(assert_list.begin(), assert_list.end(), *it);
      if(finditer==worklist.end() && iterassert==assert_list.end())
      {
        // never seen this statement before
        push(*it);
        push_into_assertion_list(assert_worklist, *it);
      }
    }
  }


#ifdef DEBUG
   std::cout << "The content of the sliced but unordered worklist is as follows: " << std::endl;
    for(std::list<acdl_domaint::statementt>::const_iterator it=worklist.begin(); it!=worklist.end(); ++it) {
    std::cout << "Sliced Unordered Worklist Element::" << from_expr(SSA.ns, "", *it) << std::endl;
    }
#endif

  // order the leaf nodes right after all assertions
  for(std::list<acdl_domaint::statementt>::const_iterator
    it=worklist.begin(); it!=worklist.end(); ++it)
  {
    if(it->id()==ID_equal) {
     exprt expr_rhs=to_equal_expr(*it).rhs();
     if(expr_rhs.id()==ID_constant || expr_rhs.is_true() || expr_rhs.is_false()) {
       push_into_list(leaf_worklist, *it);
     }
     else if(expr_rhs.type().id()!=ID_constant) {
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
    it=worklist.begin(); it!=worklist.end(); ++it)
  {
    // Do we need to separately treat ID_constraint ?
    if(it->id()==ID_equal) {
     exprt expr_rhs=to_equal_expr(*it).rhs();
     if(expr_rhs.id()==ID_constant)
       push_into_list(leaf_worklist, *it);
    // We do not push nondet elements in to the worklist
    /* std::string str("nondet");
     std::string rhs_str=id2string(expr_rhs.get(ID_identifier));
    std::size_t found=rhs_str.find(str);
    // push the nondet statement in rhs
    if(found!=std::string::npos)
      push_into_list(leaf_worklist, *it);
    */
     // exprt expr_rhs=expr.rhs();
     // select vars in the present statement
     acdl_domaint::varst vars_rhs;
     select_vars (expr_rhs, vars_rhs);

     for(std::list<acdl_domaint::statementt>::const_iterator it1=worklist.begin(); it1!=worklist.end(); ++it1)
      {
        if(*it==*it1) continue;
        /*else {
         if(!(check_statement(*it1, vars_rhs))) {
           // *it is a leaf node
           // push_into_worklist(leaf_worklist, *it);
        }*/
         // this is an intermediate node, not leaf
         else {
           // pop the element from the list
           // const acdl_domaint::statementt statement=pop_from_worklist(worklist);
           push_into_list(inter_worklist, *it);
         }
      }
    }
  }
#endif

#ifdef DEBUG
    for(std::list<acdl_domaint::statementt>::const_iterator it=leaf_worklist.begin(); it!=leaf_worklist.end(); ++it) {
    std::cout << "Leaf Element::" << from_expr(SSA.ns, "", *it) << std::endl;
    }
    for(std::list<acdl_domaint::statementt>::const_iterator it=inter_worklist.begin(); it!=inter_worklist.end(); ++it) {
    std::cout << "Intermediate Worklist Element::" << from_expr(SSA.ns, "", *it) << std::endl;
    }
#endif
  // Now prepare the final worklist
  worklist.clear();

#if 0
  // insert assertions
  // Push the negation of the assertions into the worklist
  unsigned int size=and_expr.size();
  exprt::operandst::const_iterator it=and_expr.begin();
  if(size==1) {
    exprt::operandst::const_iterator it=and_expr.begin();
#ifdef DEBUG
    std::cout << "First single assertion push: " << *it << std::endl;
#endif
    exprt exp=*it;
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
#endif
  // push the assertion and additional constriant
  // in to the worklist
  worklist.push_back(not_exprt(assertion));
  if(additional_constraint!=true_exprt())
   worklist.push_back(additional_constraint);

  acdl_domaint::varst var_leaf;
  // insert leaf nodes
  while(!leaf_worklist.empty() > 0) {
    const acdl_domaint::statementt statement=pop_from_list(leaf_worklist);
    push_into_list (worklist, statement);
    acdl_domaint::varst lvars;
    find_symbols(statement, lvars);
    var_leaf.insert(lvars.begin(), lvars.end());
  }

  // insert intermediate nodes
  while(!inter_worklist.empty() > 0) {
    const acdl_domaint::statementt statement=pop_from_list(inter_worklist);
    push_into_list (worklist, statement);
    // push into worklist_vars
    acdl_domaint::varst avars;
    find_symbols(statement, avars);
    // do not insert any leaf variables
    for(acdl_domaint::varst::const_iterator it=avars.begin(); it!=avars.end(); ++it) {
     if(var_leaf.find(*it)==var_leaf.end())
       worklist_vars.insert(*it);
    }
  }

#ifdef DEBUG
   std::cout << "The content of the ordered worklist is as follows: " << std::endl;
    for(std::list<acdl_domaint::statementt>::const_iterator
      it=worklist.begin(); it!=worklist.end(); ++it)
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
  for (local_SSAt::nodest::const_iterator n_it=SSA.nodes.begin ();
      n_it!=SSA.nodes.end (); n_it++)
  {
    for (local_SSAt::nodet::assertionst::const_iterator a_it=
        n_it->assertions.begin (); a_it!=n_it->assertions.end (); a_it++)
    {
       and_expr.push_back(*a_it);
    }
  }
  unsigned int size=and_expr.size();
#ifdef DEBUG
  std::cout << "The number of Assertions are : " << size << std::endl;
#endif
  exprt::operandst::const_iterator it=and_expr.begin();
  std::cout << "First single assertion push: " << *it << std::endl;
  if(size==1) {
    exprt::operandst::const_iterator it=and_expr.begin();
#ifdef DEBUG
    std::cout << "First single assertion push: " << *it << std::endl;
#endif
    exprt exp=*it;
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

\*************************************************************/

void
acdl_worklist_orderedt::dec_update (const local_SSAt &SSA, const acdl_domaint::meet_irreduciblet &stmt, const exprt& assertion)
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
  // compute fixpoint mu X. assert_nodes u predecessor(X)
  while(!assert_worklist.empty() > 0) {
    // collect all the leaf nodes
    const acdl_domaint::statementt statement=pop_from_list(assert_worklist);

    // select vars in the present statement
    acdl_domaint::varst vars;
    select_vars (statement, vars);
    // compute the predecessors
    update(SSA, vars, predecs_worklist, statement, assertion);

    // std::list<acdl_domaint::statementt>::iterator
    //  iterassert=std::find(assert_list.begin(), assert_list.end(), statement);

    for(std::list<acdl_domaint::statementt>::const_iterator
      it=predecs_worklist.begin(); it!=predecs_worklist.end(); ++it) {
      std::list<acdl_domaint::statementt>::iterator finditer=
                  std::find(worklist.begin(), worklist.end(), *it);

      // This is required to prevent inserting
      // individual assertions to the worklist
      std::list<acdl_domaint::statementt>::iterator iterassert=
        std::find(assert_list.begin(), assert_list.end(), *it);
      if(finditer==worklist.end() && iterassert==assert_list.end())
      {
        // never seen this statement before
        push(*it);
        push_into_assertion_list(assert_worklist, *it);
        // push into map
        live_var_list.clear();
        push_into_map(*it, live_var_list);
      }
    }
  }
#ifdef DEBUG
   std::cout << "The content of the sliced but unordered worklist is as follows: " << std::endl;
    for(std::list<acdl_domaint::statementt>::const_iterator it=worklist.begin(); it!=worklist.end(); ++it) {
    std::cout << "Sliced Unordered Worklist Element::" << from_expr(SSA.ns, "", *it) << std::endl;
    }
#endif

  // order the leaf nodes right after all assertions

  // order the leaf nodes right after all assertions
  for(std::list<acdl_domaint::statementt>::const_iterator
    it=worklist.begin(); it!=worklist.end(); ++it)
  {
    if(it->id()==ID_equal) {
     exprt expr_rhs=to_equal_expr(*it).rhs();
     if(expr_rhs.id()==ID_constant || expr_rhs.is_true() || expr_rhs.is_false()) {
       push_into_list(leaf_worklist, *it);
     }
     else if(expr_rhs.type().id()!=ID_constant) {
       push_into_list(inter_worklist, *it);
     }
    }
    else {
       push_into_list(inter_worklist, *it);
    }
  }


 #if 0

  for(std::list<acdl_domaint::statementt>::const_iterator
    it=worklist.begin(); it!=worklist.end(); ++it)
  {
    if(it->id()==ID_equal) {
     exprt expr_rhs=to_equal_expr(*it).rhs();
     if(expr_rhs.type().id()==ID_constant) {
       std::cout << "The type is " << expr_rhs.type().id() << std::endl;
       std::cout << "pushing equalities into leaf" << std::endl;
       push_into_list(leaf_worklist, *it);
     }
     else if(expr_rhs.type().id()!=ID_constant) {
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
    if(it->id()==ID_equal) {
     exprt expr_rhs=to_equal_expr(*it).rhs();
     if(expr_rhs.id()==ID_constant)
       push_into_list(leaf_worklist, *it);
    // We do not push nondet elements in to the worklist
    /* std::string str("nondet");
     std::string rhs_str=id2string(expr_rhs.get(ID_identifier));
    std::size_t found=rhs_str.find(str);
    // push the nondet statement in rhs
    if(found!=std::string::npos)
      push_into_list(leaf_worklist, *it);
    */
     // exprt expr_rhs=expr.rhs();
     // select vars in the present statement
     acdl_domaint::varst vars_rhs;
     select_vars (expr_rhs, vars_rhs);

     for(std::list<acdl_domaint::statementt>::const_iterator it1=worklist.begin(); it1!=worklist.end(); ++it1)
      {
        if(*it==*it1) continue;
        else {
         /*if(!(check_statement(*it1, vars_rhs))) {
           // *it is a leaf node
           // push_into_worklist(leaf_worklist, *it);
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
    for(std::list<acdl_domaint::statementt>::const_iterator it=leaf_worklist.begin(); it!=leaf_worklist.end(); ++it) {
    std::cout << "Leaf Element::" << from_expr(SSA.ns, "", *it) << std::endl;
    }
    for(std::list<acdl_domaint::statementt>::const_iterator it=inter_worklist.begin(); it!=inter_worklist.end(); ++it) {
    std::cout << "Intermediate Worklist Element::" << from_expr(SSA.ns, "", *it) << std::endl;
    }
#endif
  // Now prepare the final worklist
  // empty the worklist
  /*while(!worklist.empty() > 0)
    const acdl_domaint::statementt statement=pop_from_worklist(assert_worklist);
  */
  worklist.clear();
  // insert decisions as the first statement
  // worklist.push_back(stmt);

  acdl_domaint::varst dec_vars;
  // find all symbols in the decision expression
  find_symbols(stmt, dec_vars);
  live_variables.insert(dec_vars.begin(), dec_vars.end());
  // insert leaf nodes
  while(!leaf_worklist.empty() > 0) {
    const acdl_domaint::statementt statement=pop_from_list(leaf_worklist);
    push_into_list (worklist, statement);
    acdl_domaint::varst leaf_vars;
    std::set<exprt> lvars;

    // find all symbols in the leaf expression
    find_symbols(statement, leaf_vars);
    live_variables.insert(leaf_vars.begin(), leaf_vars.end());
    // push into map
    // Note: The whole live variable set is pushed into map
    // for initialization since we do not know the exact live
    // variable set for dec_update
    push_into_map(statement, live_variables);

    // find_symbols(statement, lvars);
  }

  // insert intermediate nodes
  while(!inter_worklist.empty() > 0) {
    const acdl_domaint::statementt statement=pop_from_list(inter_worklist);
    push_into_list (worklist, statement);
    acdl_domaint::varst inter_vars;
    // find all symbols in the intermediate expression
    find_symbols(statement, inter_vars);
    live_variables.insert(inter_vars.begin(), inter_vars.end());
    // push into map
    // Note: The whole live variable set is pushed into map
    // for initialization since we do not know the exact live
    // variable set for dec_update
    push_into_map(statement, live_variables);
  }

#ifdef DEBUG
   std::cout << "The content of the ordered worklist is as follows: " << std::endl;
    for(std::list<acdl_domaint::statementt>::const_iterator
      it=worklist.begin(); it!=worklist.end(); ++it)
    std::cout << "Worklist Element::" << from_expr(SSA.ns, "", *it) << std::endl;
#endif

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
                               const acdl_domaint::statementt &current_statement,
                               const exprt& assertion)
{

  // dependency analysis loop for equalities
  /*for (local_SSAt::nodest::const_iterator n_it=SSA.nodes.begin ();
      n_it!=SSA.nodes.end (); n_it++)*/

  // handle the assertion first
  if(assertion!=current_statement) {
    if (check_statement (assertion, vars)) {
      push_into_list (lexpr, not_exprt (assertion));
#ifdef DEBUG
      std::cout << "Push: " << from_expr (SSA.ns, "", not_exprt(assertion)) << std::endl;
#endif
    }
  }

  // handle other statements
  for(statement_listt::iterator it=statements.begin(); it!=statements.end(); it++)
  {
    if(*it==current_statement) continue;

    /*for (local_SSAt::nodet::equalitiest::const_iterator e_it=
        n_it->equalities.begin (); e_it!=n_it->equalities.end (); e_it++)*/
    if(it->id()==ID_equal)
    {
      exprt expr_rhs=to_equal_expr(*it).rhs();
      std::string str("nondet");
      std::string rhs_str=id2string(expr_rhs.get(ID_identifier));
      std::size_t found=rhs_str.find(str);
      // push the nondet statement in rhs
      if(found!=std::string::npos) {
      #ifdef DEBUG
        // std::cout << "Not inserting nondet elements " << std::endl;
      #endif
       continue;
      }
      // the statement has already been processed, so no action needed
      if(*it==current_statement) continue;

      if (check_statement (*it, vars)) {
        push_into_list (lexpr, *it);
        #ifdef DEBUG
        std::cout << "Push: " << from_expr (SSA.ns, "", *it) << std::endl;
        #endif
      }
    }

    /*for (local_SSAt::nodet::constraintst::const_iterator c_it=
        n_it->constraints.begin (); c_it!=n_it->constraints.end (); c_it++) */
    // handle constraints
    else
    {
      #if 0
      // handle the assertion first
      if(assertion!=current_statement && flag==false) {
        if (check_statement (assertion, vars)) {
          push_into_list (lexpr, not_exprt (assertion));
#ifdef DEBUG
          std::cout << "Push: " << from_expr (SSA.ns, "", not_exprt(assertion)) << std::endl;
#endif
         flag=true;
         continue;
        }
      }
      #endif
      if(check_statement (*it, vars)) {
        push_into_list (lexpr, *it);
        #ifdef DEBUG
        std::cout << "Push: " << from_expr (SSA.ns, "", *it) << std::endl;
        #endif
      }
    }
  #if 0
    for (local_SSAt::nodet::assertionst::const_iterator a_it=
        n_it->assertions.begin (); a_it!=n_it->assertions.end (); a_it++)
    {
      // for now, store the decision variable as variables
      // that appear only in properties
      // find all variables in an assert statement
      // assert_listt alist;
      // push_into_assertion_list(alist, *a_it);
      if(*a_it==current_statement) continue;
      if (check_statement (*a_it, vars)) {
        push_into_list (lexpr, not_exprt (*a_it));
        #ifdef DEBUG
        std::cout << "Push: " << from_expr (SSA.ns, "", not_exprt(*a_it)) << std::endl;
        #endif
      }
    }
  #endif
  }
}

/*******************************************************************\

  Function: acdl_worklist_orderedt::pop_from_worklist()

  Inputs:

  Outputs:

  Purpose:

\*******************************************************************/

acdl_domaint::varst acdl_worklist_orderedt::pop_from_map (const acdl_domaint::statementt &statement)
{
  std::map<acdl_domaint::statementt, acdl_domaint::varst>::iterator itf;
  itf=svpair.find(statement);
  acdl_domaint::varst lvars=itf->second;
  // svpair.erase(itf);
  return lvars;
}

/*******************************************************************\

Function: acdl_worklist_baset::update_worklist()

  Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/


void acdl_worklist_orderedt::update (const local_SSAt &SSA,
                               const acdl_domaint::varst &vars,
                               const acdl_domaint::statementt &current_statement,
                               const exprt& assertion)
{
  live_variables.insert(vars.begin(), vars.end());
  // [NORMAL CASE] Delete map element since corresponding worklist
  // element is also deleted.
  delete_from_map(current_statement);

  // [SPECIAL CASE] for empty deductions,
  // do not delete map elements for the current_statement
  // very conservative approach -- no chance of any
  // missing deduction, can lead to non-termination
  #if 0
  if(!vars.empty())
   delete_from_map(current_statement);
  else
   {}
  #endif

  // handle assertions first
  if(assertion!=current_statement) {
    push_into_assertion_list(alist, assertion);
    if (check_statement (assertion, vars)) {
      push(not_exprt (assertion));
      // push into map
      push_into_map(not_exprt(assertion), vars);
      acdl_domaint::varst assert_vars;
      find_symbols(assertion, assert_vars);
#ifdef DEBUG
      std::cout << "Push: " << from_expr (SSA.ns, "", not_exprt(assertion)) << std::endl;
#endif
    }
  }

  // dependency analysis loop for equalities
  /* for (local_SSAt::nodest::const_iterator n_it=SSA.nodes.begin ();
      n_it!=SSA.nodes.end (); n_it++) */
  for(statement_listt::iterator it=statements.begin(); it!=statements.end(); it++)
  {
    /*if(n_it->enabling_expr!=SSA.get_enabling_exprs())
    {
#ifdef DEBUG
      std::cout << "The enabling expression for node is " << from_expr(SSA.ns, "", n_it->enabling_expr) << std::endl;
#endif
      continue;
    }*/
    if(*it==current_statement) continue;

    /*for (local_SSAt::nodet::equalitiest::const_iterator e_it=
        n_it->equalities.begin (); e_it!=n_it->equalities.end (); e_it++)*/

    if(it->id()==ID_equal)
    {
      statement_listt::iterator e_it=it;
      exprt expr_rhs=to_equal_expr(*e_it).rhs();
      // if(expr_rhs.id()==ID_constant) {
       std::string str("nondet");
       std::string rhs_str=id2string(expr_rhs.get(ID_identifier));
       std::size_t found=rhs_str.find(str);
       // push the nondet statement in rhs
       if(found!=std::string::npos) {
        #ifdef DEBUG
        // std::cout << "Not inserting nondet elements " << std::endl;
        #endif
        continue;
       }
      // the statement has already been processed, so no action needed
      // [CHECK if NEEDED, sometimes some deduction may miss due to this]
      if(*e_it==current_statement) continue;

      if (check_statement (*e_it, vars)) {
        push(*e_it);
        // push into map
        push_into_map(*e_it, vars);
        acdl_domaint::varst equal_vars;
        find_symbols(*e_it, equal_vars);
        live_variables.insert(equal_vars.begin(), equal_vars.end());
        #ifdef DEBUG
        std::cout << "Push: " << from_expr (SSA.ns, "", *e_it) << std::endl;
        #endif
      }
    }
    /*for (local_SSAt::nodet::constraintst::const_iterator c_it=
        n_it->constraints.begin (); c_it!=n_it->constraints.end (); c_it++) */
    // handle constraints
    else
    {
      statement_listt::iterator c_it=it;
      // [CHECK if NEEDED]
      if(*c_it==current_statement) continue;
      if (check_statement (*c_it, vars)) {
        push(*c_it);
        // push into map
        push_into_map(*c_it, vars);
        acdl_domaint::varst constraint_vars;
        find_symbols(*c_it, constraint_vars);
        live_variables.insert(constraint_vars.begin(), constraint_vars.end());

        #ifdef DEBUG
        std::cout << "Push: " << from_expr (SSA.ns, "", *c_it) << std::endl;
        #endif
      }
    }

#if 0
    for (local_SSAt::nodet::assertionst::const_iterator a_it=
        n_it->assertions.begin (); a_it!=n_it->assertions.end (); a_it++)
    {
      // for now, store the decision variable as variables
      // that appear only in properties
      // find all variables in an assert statement
      // assert_listt alist;
      push_into_assertion_list(alist, *a_it);

      if(*a_it==current_statement) continue;
      if (check_statement (*a_it, vars)) {
        push(not_exprt (*a_it));
        acdl_domaint::varst assert_vars;
        find_symbols(*a_it, assert_vars);
        live_variables.insert(assert_vars.begin(), assert_vars.end());

        #ifdef DEBUG
        std::cout << "Push: " << from_expr (SSA.ns, "", not_exprt(*a_it)) << std::endl;
        #endif
      }
    }
#endif
   #if 0
    // Push the assertion that is passed to the solver
    push_into_assertion_list(alist, assertion);
    if(assertion==current_statement) continue;
    if (check_statement (assertion, vars)) {
      push(not_exprt (assertion));
      // push into map
      push_into_map(not_exprt(assertion), vars);
      acdl_domaint::varst assert_vars;
      find_symbols(assertion, assert_vars);
#ifdef DEBUG
      std::cout << "Push: " << from_expr (SSA.ns, "", not_exprt(assertion)) << std::endl;
#endif
    }
#endif
  } // end for

 // remove variables of popped statement from live variables
 remove_live_variables(SSA, current_statement);

#ifdef DEBUG
 std::cout << "The content of the updated worklist is as follows: " << std::endl;
 for(std::list<acdl_domaint::statementt>::const_iterator
     it=worklist.begin(); it!=worklist.end(); ++it) {
   std::cout << "Updated Worklist Element::" << from_expr(SSA.ns, "", *it) << "===>";
   std::map<acdl_domaint::statementt, acdl_domaint::varst>::iterator itf;
   itf=svpair.find(*it);
   acdl_domaint::varst lvar=itf->second;
   for(acdl_domaint::varst::const_iterator it1=
       lvar.begin(); it1!=lvar.end(); ++it1)
     std::cout << from_expr(*it1) << ", ";
   std::cout << std::endl;
 }
#endif


#ifdef DEBUG
  std::cout << "The updated live variables after removal are as follows: ";
  for(acdl_domaint::varst::const_iterator it=
    live_variables.begin(); it!=live_variables.end(); ++it)
   std::cout << from_expr(SSA.ns, "", *it);
   std::cout << " " << std::endl;
#endif

}
