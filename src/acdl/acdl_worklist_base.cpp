/*******************************************************************\

Module: ACDL Worklist Management Base

Author: Rajdeep Mukherjee, Peter Schrammel

 \*******************************************************************/

#include <util/find_symbols.h>
#include "acdl_worklist_base.h"

//#define DEBUG


#ifdef DEBUG
#include <iostream>
#endif

/*******************************************************************\

Function: acdl_worklist_baset::push_into_assertion_list()

  Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

void
acdl_worklist_baset::push_into_assertion_list (assert_listt &aexpr,
				  const acdl_domaint::statementt &statement)
{
  aexpr.push_back(statement);
}

/*******************************************************************	\

Function: acdl_worklist_baset::check_statement()

  Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

bool
acdl_worklist_baset::check_statement (const exprt &expr,
                               const acdl_domaint::varst &vars)
{

  std::set<symbol_exprt> symbols;
  // find all variables in a statement
  find_symbols (expr, symbols);
  // check if vars appears in the symbols set,
  // if there is a non-empty intersection, then insert the
  // equality statement in the worklist
  for (acdl_domaint::varst::const_iterator it = vars.begin ();
      it != vars.end (); it++)
  {
    if (symbols.find (*it) != symbols.end ())
    {
      // find_symbols here may be required to 
      // find transitive dependencies
      // in which case make vars non-constant
      //find_symbols(expr, vars);
      return true;
    }
  }
  return false;
}

/*******************************************************************\

Function: acdl_worklist_baset::push_into_worklist()

  Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

void
acdl_worklist_baset::push (const acdl_domaint::statementt &statement)
{
#ifdef DEBUG  
  std::cout << "Pushing into worklist " << from_expr(statement) << std::endl;
#endif  
  for(worklistt::const_iterator it = worklist.begin();
      it != worklist.end(); ++it) {
    if(statement == *it)
      return;
  }
#ifdef DEBUG  
  std::cout << "Push element into worklist " << from_expr(statement) << std::endl;
#endif  
  worklist.push_back(statement);
}

/*******************************************************************\

  Function: acdl_worklist_baset::push_into_map()

  Inputs:

  Outputs:

  Purpose: 

 \*******************************************************************/

void
acdl_worklist_baset::push_into_map (const acdl_domaint::statementt &statement, const acdl_domaint::varst &lvars)
{
#ifdef DEBUG  
  std::cout << "Pushing in to map" << std::endl;
  std::cout << "Statement is " << from_expr(statement) << " ===> "; 
  for(acdl_domaint::varst::const_iterator it1 = 
      lvars.begin(); it1 != lvars.end(); ++it1)
    std::cout << from_expr(*it1) << ", "; 
  std::cout << std::endl;
#endif

  std::map<acdl_domaint::statementt,acdl_domaint::varst>::iterator itf; 
  itf = svpair.find(statement);
  if(itf != svpair.end()) {} // handle later
  else {
    svpair.insert(make_pair(statement, lvars));   
  }

  // iterate over whole map and 
  // update the live varaibles
  for(std::map<acdl_domaint::statementt, acdl_domaint::varst>::iterator
    it=svpair.begin(); it!=svpair.end(); ++it) {
#if 0   
   // check if statement already exists
   if(it->first == statement) {
     // check the live var list 
     // only add live variables not present
     acdl_domaint::varst live_vars = it->second;
     for(acdl_domaint::varst::const_iterator it1 = 
         lvars.begin(); it1 != lvars.end(); ++it1)
     {
       acdl_domaint::varst::iterator lit = live_vars.find(*it1); 
       if(lit == live_vars.end()) live_vars.insert(*it1);
       else continue;
     }
   }
   // for other statements, simply 
   // update the live varaibles if not present
   else {
#endif
#ifdef DEBUG          
     std::cout << "Looping over map statement: " << from_expr(it->first) << std::endl; 
     
#endif
     acdl_domaint::varst live_vars = it->second;
     for(acdl_domaint::varst::const_iterator it1 = 
         lvars.begin(); it1 != lvars.end(); ++it1)
     {
#ifdef DEBUG          
       std::cout << "Checking deduction vars" << from_expr(*it1) << " ,";
#endif       
       acdl_domaint::varst::iterator lit = live_vars.find(*it1); 
       if(lit == live_vars.end()) {
#ifdef DEBUG          
         std::cout << "insert in to live vars" << std::endl;
#endif         
         it->second.insert(*it1);
       }
       else continue;
     }
   //}
  }
#if 0  
  std::map<acdl_domaint::statementt,acdl_domaint::varst>::iterator itf; 
  itf = svpair.find(statement);
  if(itf != svpair.end()) {
    // check the live var list 
    // only add live variables not present
    acdl_domaint::varst live_vars = itf->second;
    for(acdl_domaint::varst::const_iterator it1 = 
        lvars.begin(); it1 != lvars.end(); ++it1)
    {
      acdl_domaint::varst::iterator lit = live_vars.find(*it1); 
      if(lit == live_vars.end()) live_vars.insert(*it1);
      else continue;
    }
  }
  else
  {
    svpair.insert(make_pair(statement, lvars));   
  }
#endif  
}

/*******************************************************************\

  Function: acdl_worklist_baset::delete_map()

  Inputs:

  Outputs:

  Purpose:

\*******************************************************************/

void acdl_worklist_baset::delete_map()
{    
  while(!svpair.empty())
   svpair.erase(svpair.begin());
}

/*******************************************************************\

  Function: acdl_worklist_baset::delete_from_map()

  Inputs:

  Outputs:

  Purpose:

\*******************************************************************/

void acdl_worklist_baset::delete_from_map (const acdl_domaint::statementt &statement)
{
  std::map<acdl_domaint::statementt,acdl_domaint::varst>::iterator itf; 
  itf = svpair.find(statement);
  svpair.erase(itf);
}


/*******************************************************************\

Function: acdl_worklist_baset::check_var_liveness()

  Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

acdl_domaint::varst acdl_worklist_baset::check_var_liveness (acdl_domaint::varst &vars)
{
  
  for(acdl_domaint::varst::const_iterator it = 
    vars.begin(); it != vars.end(); ++it)
  {
    acdl_domaint::varst::iterator it1 = live_variables.find(*it);
    if(it1 == live_variables.end()) vars.erase(*it);
  }
  return vars;
}


/*******************************************************************\

Function: acdl_worklist_baset::remove_live_variables()

  Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

void acdl_worklist_baset::remove_live_variables 
  (const local_SSAt &SSA, const acdl_domaint::statementt &statement)
{
#ifdef DEBUG
        std::cout << "Popped Statement for live variables: " 
        << from_expr (SSA.ns, "", statement) << std::endl;
#endif
  
  // remove variables in statement from live variables
  acdl_domaint::varst del_vars;
  find_symbols(statement, del_vars);  
#ifdef DEBUG
  std::cout << "Variables in Popped Statement: "; 
  for(acdl_domaint::varst::const_iterator it = 
    del_vars.begin(); it != del_vars.end(); ++it)
      std::cout << from_expr (SSA.ns, "", *it) << " ";
  std::cout << " " << std::endl;
#endif

#ifdef DEBUG   
  std::cout << "Live variables list are as follows: ";
  for(acdl_domaint::varst::const_iterator it = 
    live_variables.begin(); it != live_variables.end(); ++it)
   std::cout << from_expr(SSA.ns, "", *it); 
   std::cout << " " << std::endl;
#endif
  bool found = false;
  for(acdl_domaint::varst::const_iterator it = 
    del_vars.begin(); it != del_vars.end(); ++it) {
   found = false;
   for(std::list<acdl_domaint::statementt>::const_iterator 
      it1 = worklist.begin(); it1 != worklist.end(); ++it1)
   {
     acdl_domaint::varst find_vars;
     find_symbols(*it1, find_vars);
     acdl_domaint::varst::const_iterator it2 = find_vars.find(*it);   
     if(it2 != find_vars.end()) {found = true; break; }
   }  
   if(found == false)   
   {
#ifdef DEBUG
        std::cout << "Deleted live variables are: " 
        << from_expr (SSA.ns, "", *it) << std::endl;
#endif
       live_variables.erase(*it);
   }
  }
}


/*******************************************************************\

Function: acdl_worklist_baset::pop_from_worklist()

  Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

const acdl_domaint::statementt
acdl_worklist_baset::pop ()
{
#if 1
  const acdl_domaint::statementt statement = worklist.front();
  worklist.pop_front();
#else
  worklistt::iterator it = worklist.begin ();
  const exprt statement = *it;
  worklist.erase (it);
#endif
  return statement;
}

/*******************************************************************

 Function: acdl_worklist_baset::select_vars()

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

void
acdl_worklist_baset::select_vars (const exprt &statement, acdl_domaint::varst &vars)
{
#if 0 //TODO: this was an attempt to implement a forward iteration strategy,
      //      but we would also need to consider execution order 
  // If it is an equality, then select the lhs for post-condition computation
  exprt lhs;
  if (statement.id () == ID_equal)
  {
    lhs = to_equal_expr (statement).lhs ();
    if (lhs.id () == ID_symbol)
    {
      vars.insert (to_symbol_expr (lhs));
    }
    else //TODO: more complex lhs
      assert(false);
  }
  else // for constraints
#endif
  {
    find_symbols(statement,vars);
  }
}

/*******************************************************************\

Function: acdl_worklist_orderedt::initialize()

  Inputs:

 Outputs:

 Purpose: Initialize the worklist

 \*******************************************************************/

void
acdl_worklist_baset::initialize_live_variables ()
{
  //Strategy 0: initialize live variables for each 
  //statement by adding all live variables
  for(std::list<acdl_domaint::statementt>::const_iterator 
      it = worklist.begin(); it != worklist.end(); ++it) {
    acdl_domaint::varst insert_vars;
    select_vars(*it, insert_vars);
    for(acdl_domaint::varst::const_iterator it1 = 
        insert_vars.begin(); it1 != insert_vars.end(); ++it1)
      live_variables.insert(*it1);   
  }
  // insert all live variables for each statement
  for(std::list<acdl_domaint::statementt>::const_iterator 
    it = worklist.begin(); it != worklist.end(); ++it)
  {
    svpair.insert(make_pair(*it, live_variables)); 
  }
#ifdef DEBUG          
  std::cout << "Printing the initialized map" << std::endl;
#endif   
#ifdef DEBUG          
  for(std::map<acdl_domaint::statementt, acdl_domaint::varst>::iterator
    it=svpair.begin(); it!=svpair.end(); ++it) {
    std::cout << "Statement is " << from_expr(it->first) << "==>";
    acdl_domaint::varst live_vars = it->second;
    for(acdl_domaint::varst::const_iterator it1 = 
        live_vars.begin(); it1 != live_vars.end(); ++it1)
      std::cout << from_expr(*it1) << ", "; 
      std::cout << std::endl;
  }
#endif     
#if 0  
  //Strategy 1: initialize live variables by adding all vars
  for(std::list<acdl_domaint::statementt>::const_iterator 
      it = worklist.begin(); it != worklist.end(); ++it) {
    acdl_domaint::varst insert_vars;
    select_vars(*it, insert_vars);
    for(acdl_domaint::varst::const_iterator it1 = 
        insert_vars.begin(); it1 != insert_vars.end(); ++it1)
      live_variables.insert(*it1);   
  }
#endif
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
 
#if 0
  std::cout << "Printing all live variables" << std::endl;
  for(acdl_domaint::varst::const_iterator 
    it = live_variables.begin(); it != live_variables.end(); ++it)
      std::cout << it->get_identifier() << "," << std::endl;
#endif
}   
  
/*******************************************************************\

Function: acdl_worklist_orderedt::print()

 Inputs:

 Outputs:

 Purpose: Print the worklist

 \*******************************************************************/

void acdl_worklist_baset::print_worklist() 
{
#ifdef DEBUG  
  std::cout << "Printing the worklist" << std::endl; 
#endif  
  for(std::list<acdl_domaint::statementt>::const_iterator 
      it = worklist.begin(); it != worklist.end(); ++it)
    std::cout << from_expr(*it) <<  "," << std::endl;
  std::cout << std::endl; 
}


/*******************************************************************\

  Function: acdl_worklist_baset::slicing()

  Inputs:

  Outputs:

  Purpose: Slice with respect to assertion

\*******************************************************************/

void
acdl_worklist_baset::slicing (const local_SSAt &SSA, 
        const exprt &assertion, const exprt& additional_constraint)
{
  typedef std::list<acdl_domaint::statementt> initial_worklistt;
  initial_worklistt initial_worklist; 
  typedef std::list<acdl_domaint::statementt> predecs_worklistt;
  predecs_worklistt predecs_worklist; 
  typedef std::list<acdl_domaint::statementt> final_worklistt;
  final_worklistt final_worklist; 
#ifdef DEBUG
  std::cout << "Performing Slicing w.r.t. assertion" << std::endl;
#endif    
  // push the assertion in to the intial worklist
  push_into_list(initial_worklist, assertion);
  // Now compute the transitive dependencies
  //compute fixpoint mu X. assert_nodes u predecessor(X)
  while(!initial_worklist.empty() > 0) {
    // collect all the leaf nodes
    const acdl_domaint::statementt statement = pop_from_list(initial_worklist);

    // select vars in the present statement
    acdl_domaint::varst vars;
    select_vars (statement, vars);
    // compute the predecessors
#ifdef DEBUG 
    std::cout << "Computing predecessors of statement " << 
               from_expr(statement) << std::endl;
#endif        
    update(SSA, vars, predecs_worklist, statement, assertion);
    
    for(std::list<acdl_domaint::statementt>::const_iterator 
      it = predecs_worklist.begin(); it != predecs_worklist.end(); ++it) {
      std::list<acdl_domaint::statementt>::iterator finditer = 
                  std::find(final_worklist.begin(), final_worklist.end(), *it); 
    
      if(finditer == final_worklist.end() && *it != statement)
      {
        // push the sliced statements 
        // into final worklist for later processing
        push_into_list(final_worklist, *it);
        // never seen this statement before
        push_into_list(initial_worklist, *it);
      }
    }
  }
  
//#ifdef DEBUG    
   std::cout << "The content of the sliced worklist is as follows: " << std::endl;
   for(std::list<acdl_domaint::statementt>::const_iterator 
         it = final_worklist.begin(); it != final_worklist.end(); ++it) {
	    std::cout << from_expr(SSA.ns, "", *it) << std::endl;
   }
//#endif    

  // flush out the content in statements
  statements.clear();
  
  // now collect all sliced statements
  for(std::list<acdl_domaint::statementt>::const_iterator 
        it = final_worklist.begin(); it != final_worklist.end(); ++it) {
    if(*it == assertion)
      statements.push_back(not_exprt(*it)); 
    else 
      statements.push_back(*it); 
  }
}

/*******************************************************************\

Function: acdl_worklist_baset::push_into_list()

  Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

void
acdl_worklist_baset::push_into_list(listt &lexpr,
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
acdl_worklist_baset::pop_from_list(listt &lexpr)
{
  const acdl_domaint::statementt statement = lexpr.front();
  lexpr.pop_front();
  return statement;
}

/*******************************************************************\

 Function: acdl_worklist_baset::update()

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

void
acdl_worklist_baset::update (const local_SSAt &SSA,
                               const acdl_domaint::varst &vars,
                               
                               listt &lexpr, 
                               const acdl_domaint::statementt &current_statement, 
                               const exprt& assertion)
{
   
  // dependency analysis loop for equalities
  /*for (local_SSAt::nodest::const_iterator n_it = SSA.nodes.begin ();
      n_it != SSA.nodes.end (); n_it++)*/
  bool flag = false;
  for(statement_listt::iterator it = statements.begin(); it != statements.end(); it++) 
  {
    if(*it == current_statement) continue;

    /*for (local_SSAt::nodet::equalitiest::const_iterator e_it =
        n_it->equalities.begin (); e_it != n_it->equalities.end (); e_it++)*/
    if(it->id() == ID_equal)    
    {
      exprt expr_rhs = to_equal_expr(*it).rhs();
      std::string str("nondet");
      std::string rhs_str=id2string(expr_rhs.get(ID_identifier));
      std::size_t found = rhs_str.find(str); 
      // push the nondet statement in rhs
      if(found != std::string::npos) {
      #ifdef DEBUG
        //std::cout << "Not inserting nondet elements " << std::endl; 
      #endif  
       continue; 
      }
      // the statement has already been processed, so no action needed
      if(*it == current_statement) continue;

      if (check_statement (*it, vars)) {
        push_into_list (lexpr, *it);
        #ifdef DEBUG
        std::cout << "Push: " << from_expr (SSA.ns, "", *it) << std::endl;
        #endif
      }
    }
    
    /*for (local_SSAt::nodet::constraintst::const_iterator c_it =
        n_it->constraints.begin (); c_it != n_it->constraints.end (); c_it++) */
    else     
    {
      if(it->id() == ID_assert) 
        std::cout << "Processing assert " << from_expr(SSA.ns, "", *it) << std::endl;
      // handle the assertion first
      if(assertion != current_statement && flag==false) {
        if (check_statement (assertion, vars)) {
          push_into_list (lexpr, not_exprt (assertion));
#ifdef DEBUG
          std::cout << "Push: " << from_expr (SSA.ns, "", not_exprt(assertion)) << std::endl;
#endif
         flag = true; 
         continue;
        }
      }
      // handle constraints
      else if(check_statement (*it, vars)) {
        push_into_list (lexpr, *it);
        #ifdef DEBUG
        std::cout << "Push: " << from_expr (SSA.ns, "", *it) << std::endl;
        #endif
      }
    }
  #if 0  
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
  #endif  
  }
}
