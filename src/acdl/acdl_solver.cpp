/*******************************************************************\

Module: ACDL Solver

Author: Rajdeep Mukherjee, Peter Schrammel

\*******************************************************************/


#include <langapi/language_util.h>
#include <util/find_symbols.h>
#include "acdl_solver.h"
#include "acdl_domain.h"
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
  //TODO: add assertions first

  
#if 1
  // check for equalities or constraints or next node
  if (SSA.nodes.empty ())
    return;
  assert(!SSA.nodes.front ().equalities.empty ());
  // insert the first element on to the worklist
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
  exprt decision_expr; //TODO: This characterize the shape of the decisions made, (eg. x < 5 or x-y < 5)
  exprt decision_var;
  acdl_domaint::valuet decision; // container that contains the decision (eg. x == [0,10])
  
  //TODO
  // use information from VSIDS to choose decision 'variable'
  
  // ***********************************************************************
  // Note: using CFG flow instead can be used to emulate a forward analysis
  //       This is similar to Astree simulation 
  // ***********************************************************************

  // choose a meet irreducible
  // 1. pick possible decision from source code 
  
  // *******************************************
  // 1.a. look at conditions in the SSA: cond#3
  //      decision = cond_var
  // *******************************************
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
        std::cout << "DECISION PHASE: " << from_expr (SSA.ns, "", e_it->lhs()) << std::endl;
#endif        
          decision_var = e_it->lhs();
        }
      }
    }
  }
  decision = domain.split(decision_var,decision_expr);
  std::cout << "DECISION SPLITTING VALUE: " << from_expr (SSA.ns, "", decision) << std::endl;
  equal_exprt dec_expr(decision_var, decision);
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
  g.backtrack_points[decision] = v;
  // Update the edges of the decision graph
  g.edges[decision] = g.current_node;
  g.current_node = decision;
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
