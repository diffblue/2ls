/*******************************************************************\

Module: ACDL Solver

Author: Rajdeep Mukherjee, Peter Schrammel

\*******************************************************************/


#include <langapi/language_util.h>
#include <util/find_symbols.h>
#include "acdl_solver.h"
#include "acdl_domain.h"
#include "acdl_decision_heuristics_cond.h"
#include "acdl_worklist_ordered.h"
#include <string>

#define DEBUG


#ifdef DEBUG
#include <iostream>
#endif

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
						   acdl_domaint::valuet &v)
{
  while (!worklist.empty())
  {
    const acdl_domaint::statementt statement = worklist.pop();
    
#ifdef DEBUG
    std::cout << "Pop: " << from_expr (SSA.ns, "", statement)
        << std::endl;
#endif

    // select vars according to iteration strategy
    acdl_domaint::varst vars;
    worklist.select_vars (statement, vars);
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
    //TODO: update implication graph
    clause_learning.add_deductions(new_v);
    //TODO: update worklist based on variables in the consequent

    // terminating condition check for populating worklist
    if(!domain.contains(v, new_v)) //TODO: remove
    {
      worklist.update(SSA, vars, statement);
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
		      decision_grapht &g)
{

  acdl_domaint::meet_irreduciblet dec_expr=decision_heuristics(SSA, v);
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
  clause_learning.add_decisions(dec_expr);
  
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
  worklist.update(SSA, dec_vars);
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
  // PS: you must not manipulate the worklist directly 
  // here, use the methods provided by worklist
  // The below code in while loop is needed, implement pop function from worklist
  while(!worklist.empty()) { 
    //const acdl_domaint::statementt statement = worklist.front();
    //worklist.pop_front();
    worklist.pop();
  }
  // update the worklist here 
  worklist.update(SSA, learn_vars);
  
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
  worklist.initialize(SSA);

#if 0
  // collect assertion variables for completeness check: This is not sound
  std::set<symbol_exprt> assertion_vars;
  for (local_SSAt::nodest::const_iterator n_it = SSA.nodes.begin ();
      n_it != SSA.nodes.end (); n_it++)
    for (local_SSAt::nodet::assertionst::const_iterator a_it =
        n_it->assertions.begin (); a_it != n_it->assertions.end (); a_it++)
    find_symbols (*a_it, assertion_vars);
#endif

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
      result = propagate(SSA, v);

      // check for conflict
      if(result == property_checkert::PASS) //UNSAT
        break;
    
      // check for satisfying assignment
      std::set<symbol_exprt> completeness_vars;
      find_symbols (v, completeness_vars);
      if(domain.is_complete(v, completeness_vars))
        return property_checkert::FAIL;
      
      std::cout << "********************************" << std::endl;
      std::cout << "         DECISION PHASE"          << std::endl;
      std::cout << "********************************" << std::endl;
      // make a decision
      decide(SSA, v, g);
    }

    std::cout << "********************************" << std::endl;
    std::cout << "    CONFLICT ANALYSIS PHASE" << std::endl;
    std::cout << "********************************" << std::endl;

    // analyze conflict ...
    result = analyze_conflict(SSA, v, g);
    // decision level 0 conflict
    /*if(result == property_checkert::PASS) //UNSAT
      break;
    else 
      continue;*/
  }

  return result;
}
