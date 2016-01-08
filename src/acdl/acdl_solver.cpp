/*******************************************************************\

Module: ACDL Solver

Author: Rajdeep Mukherjee, Peter Schrammel

\*******************************************************************/


#include <langapi/language_util.h>
#include <util/find_symbols.h>
#include "acdl_solver.h"
#include "acdl_domain.h"
#include "acdl_decision_heuristics_cond.h"
#include <string>

#define DEBUG


#ifdef DEBUG
#include <iostream>
#endif

/*******************************************************************\

Function: acdl_solvert::operator()

  Inputs:

 Outputs:

 Purpose: Initialize the worklist

 \*******************************************************************/

void
acdl_solvert::initialize_worklist (const local_SSAt &SSA, worklistt &worklist)
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

/*******************************************************************\

Function: acdl_solvert::check_statement()

  Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

bool
acdl_solvert::check_statement (const exprt &expr,
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

Function: acdl_solvert::push_into_assertion_list()

  Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

void
acdl_solvert::push_into_assertion_list (assert_listt &aexpr,
				  const acdl_domaint::statementt &statement)
{
  aexpr.push_back(statement);
}

/*******************************************************************\

Function: acdl_solvert::push_into_worklist()

  Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

void
acdl_solvert::push_into_worklist (worklistt &worklist,
				  const acdl_domaint::statementt &statement)
{
#if 1 // list implementation
  for(worklistt::const_iterator it = worklist.begin();
      it != worklist.end(); ++it)
    if(statement == *it)
      return;
  worklist.push_back(statement);
#else // set implementation
  worklist.insert(statement);
#endif
}

/*******************************************************************\

Function: acdl_solvert::pop_from_worklist()

  Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

const acdl_domaint::statementt
acdl_solvert::pop_from_worklist (worklistt &worklist)
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

/*******************************************************************\

Function: acdl_solvert::update_worklist()

  Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/


void
acdl_solvert::update_worklist (const local_SSAt &SSA,
                               const acdl_domaint::varst &vars,
                               worklistt &worklist,
                               const acdl_domaint::statementt &current_statement)
{
  // dependency analysis loop for equalities
  for (local_SSAt::nodest::const_iterator n_it = SSA.nodes.begin ();
      n_it != SSA.nodes.end (); n_it++)
  {

    for (local_SSAt::nodet::equalitiest::const_iterator e_it =
        n_it->equalities.begin (); e_it != n_it->equalities.end (); e_it++)
    {
      // the statement has already been processed, so no action needed
      if(*e_it == current_statement) continue;

      if (check_statement (*e_it, vars)) {
        push_into_worklist(worklist, *e_it);
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
        push_into_worklist(worklist, *c_it);
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
      assert_listt alist;
      push_into_assertion_list(alist, *a_it);
           
      if(*a_it == current_statement) continue;
      if (check_statement (*a_it, vars)) {
        push_into_worklist(worklist, not_exprt (*a_it));
        #ifdef DEBUG
        std::cout << "Push: " << from_expr (SSA.ns, "", not_exprt(*a_it)) << std::endl;
        #endif
      }
    }
  }
}


/*******************************************************************

 Function: acdl_solvert::select_vars()

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

void
acdl_solvert::select_vars (const exprt &statement, acdl_domaint::varst &vars)
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

Function: acdl_solvert::propagate

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

property_checkert::resultt acdl_solvert::propagate(const local_SSAt &SSA,
						   acdl_domaint::valuet &v,
						   worklistt &worklist)
{
  while (!worklist.empty())
  {
    const acdl_domaint::statementt statement = pop_from_worklist(worklist);
    
#ifdef DEBUG
    std::cout << "Pop: " << from_expr (SSA.ns, "", statement)
        << std::endl;
#endif

    // select vars according to iteration strategy
    acdl_domaint::varst vars;
    select_vars (statement, vars);
#ifdef DEBUG
    std::cout << "Selected vars:";
    for(acdl_domaint::varst::const_iterator v_it = vars.begin();
	v_it != vars.end(); ++v_it)
      std::cout << " " << from_expr (SSA.ns, "", *v_it);
    std::cout << std::endl;
#endif

    // compute update of abstract value
    acdl_domaint::valuet new_v;
    domain (statement, vars, v, new_v);

    // terminating condition check for populating worklist
    if(!domain.contains(v, new_v))
    {
      update_worklist(SSA, vars, worklist, statement);
    }

#ifdef DEBUG
    std::cout << "Old: " << from_expr (SSA.ns, "", v)
              << std::endl;
    std::cout << "New: " << from_expr (SSA.ns, "", new_v)
              << std::endl;
#endif

    // meet is computed because we are doing gfp
    domain.meet (new_v, v);
    domain.normalize(v,vars);
    
#ifdef DEBUG
    std::cout << "Updated: " << from_expr (SSA.ns, "", v)
              << std::endl;
#endif

    //Cool! We got UNSAT
    if(domain.is_bottom(v))
    {
#ifdef DEBUG
      std::cout << "Propagation finished with BOTTOM" << std::endl;
#endif
      return property_checkert::PASS; //potential UNSAT (modulo decisions)
    }
    /*else {
      // For soundness, we decided to insert the 
      // element that is popped from the worklist
      update_worklist(SSA, vars, worklist, statement);
    }*/

  }

#ifdef DEBUG
  std::cout << "Propagation finished with UNKNOWN" << std::endl;
#endif

  return property_checkert::UNKNOWN;
}


/*******************************************************************

 Function: acdl_solvert::decide()

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

void
acdl_solvert::decide (const local_SSAt &SSA,
		      acdl_domaint::valuet &v,
		      decision_grapht &g,
		      worklistt &worklist,
		      assert_listt &alist)
{

  acdl_domaint::meet_irreduciblet dec_expr=decision(SSA, v);
  std::cout << "DECISION SPLITTING EXPR: " << from_expr (SSA.ns, "", dec_expr) << std::endl;
  // *****************************************************************
  // 1.b. e.g. we have x!=2 in an assertion or cond node, then we have 
  // meet irreducibles x<=1, x>=3 as potential decisions
  // ****************************************************************

  
  // ****************************
  // 2. call acdl_domaint::split
  // ****************************
  #if 0
  std::cout << "DECISION PHASE: " << from_expr (SSA.ns, "", alist.front()) << std::endl;
  decision = domain.split(alist.front(),decision_expr);
  #endif
  
  // update decision graph
  // TODO
  
  // keep information for backtracking associated with this decision point in g
  g.backtrack_points[dec_expr] = v;
  // Update the edges of the decision graph
  g.edges[dec_expr] = g.current_node;
  g.current_node = dec_expr;
  // Also save the decision level
  g.decision_level = 0;
  // update the deduction list
  //deduction_list.push_back(v);
  //g.propagate_list[dec_expr] = g.deduction_list;

  // Take a meet of the decision expression (decision) with the current abstract state (v).
  // The new abstract state is now in v
  domain.meet(dec_expr,v);
  

  acdl_domaint::varst dec_vars;
  // find all symbols in the decision expression
  find_symbols(dec_expr, dec_vars);
  // update the worklist here 
  update_worklist(SSA, dec_vars, worklist);
}

/*******************************************************************

 Function: acdl_solvert::analyze_conflict()

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

property_checkert::resultt 
acdl_solvert::analyze_conflict(const local_SSAt &SSA,
			       acdl_domaint::valuet &v,
             worklistt &worklist, 
			       decision_grapht &g)
{
  //TODO
  // ******* For temporary purpose **********
  exprt decision_reason;
  std::string str("cond");
  std::string lhs_str;
  for (local_SSAt::nodest::const_iterator n_it = SSA.nodes.begin ();
      n_it != SSA.nodes.end (); n_it++)
  {
    for (local_SSAt::nodet::equalitiest::const_iterator e_it =
        n_it->equalities.begin (); e_it != n_it->equalities.end (); e_it++)
    {
      const irep_idt &identifier = e_it->lhs().get(ID_identifier);
      // check if the rhs of an equality is a constant, 
      // in that case don't do anything  
      if(e_it->rhs().id() == ID_constant) {}
      else {
        lhs_str = id2string(identifier); //e_it->lhs().get(ID_identifier)); 
        std::size_t found = lhs_str.find(str);
        if (found!=std::string::npos) {
#ifdef DEBUG
          //std::cout << "DECISION PHASE: " << from_expr (SSA.ns, "", e_it->lhs()) << std::endl;
#endif        
          decision_reason = e_it->lhs();
        }
      }
    }
  }
  // ****************************************


  // first UIP over conflict graph
  //exprt decision_reason;

  // get the learned clause which is 
  // the negation of the reason of conflict
  exprt learned_clauses = not_exprt(decision_reason);
  
  // generalise learned clause
 
 #ifdef DEBUG
          std::cout << "LEARNED CLAUSE: " << from_expr (SSA.ns, "", learned_clauses) << std::endl;
 #endif        
 
    
  // backtrack
  v = g.backtrack_points[decision_reason];
  // clean up decision graph and, optionally, backtrack points

  // add learned clauses
  domain.meet(learned_clauses,v);

  acdl_domaint::varst learn_vars;
  // find all symbols in the learned clause
  find_symbols(learned_clauses, learn_vars);
  
  // RM: empty the worklist here
  while(!worklist.empty()) { 
    const acdl_domaint::statementt statement = worklist.front();
    worklist.pop_front();
  }
  // update the worklist here 
  update_worklist(SSA, learn_vars, worklist);
  
  // do propagate here (required for cond variable based decision 
  // heuristic to cover all branches in control flow)
  //property_checkert::resultt result = property_checkert::UNKNOWN;
  //result = propagate(SSA, v, worklist);

  return property_checkert::PASS;
}

/*******************************************************************
 Function: acdl_solvert::operator()

 Inputs:

 Outputs:

 Purpose:
while true do
 S = TOP;
 while true do                                    // PHASE 1: Model Search
  repeat                                          // deduction
    S <- S meet ded(S);
  until S = S meet ded(S);
  if S = bot then break ;                         // conflict
  if complete(ded,S) then return (not BOTTOM,S);  // return SAT model
   S <- decision(S);                              // make decision
 end
 L <- analyse conflict(S) ;                       // PHASE 2: Conflict Analysis
 if L= TOP then return (BOTTOM,L);                // return UNSAT
   ded <- ded meet ded_L;                         // learn: refine transformer
end
\*******************************************************************/

property_checkert::resultt acdl_solvert::operator()(const local_SSAt &SSA)
{
  worklistt worklist;
  assert_listt alist;
  initialize_worklist(SSA, worklist);


  acdl_domaint::valuet v;
  domain.set_top(v);
  decision_grapht g;
  g.current_node = nil_exprt(); // root node
    
  property_checkert::resultt result = property_checkert::UNKNOWN;
  while(result == property_checkert::UNKNOWN)
  {
    while(true)
    {
      // deduction phase in acdl
      std::cout << "********************************" << std::endl;
      std::cout << "        DEDUCTION PHASE " << std::endl;
      std::cout << "********************************" << std::endl;
      result = propagate(SSA, v, worklist);

      // check for conflict
      if(result == property_checkert::PASS) //UNSAT
        break;
    
      // check for satisfying assignment
      if(domain.is_complete(v))
        return property_checkert::FAIL;
      
      std::cout << "********************************" << std::endl;
      std::cout << "         DECISION PHASE"          << std::endl;
      std::cout << "********************************" << std::endl;
      // make a decision
      decide(SSA, v, g, worklist, alist);
    }

    std::cout << "********************************" << std::endl;
    std::cout << "    CONFLICT ANALYSIS PHASE" << std::endl;
    std::cout << "********************************" << std::endl;

    // analyze conflict ...
    result = analyze_conflict(SSA, v, worklist, g);
    /*if(result == property_checkert::PASS) //UNSAT
      break;
    else 
      continue;*/
  }

  return result;
}
