/*******************************************************************\

Module: ACDL Solver

Author: Rajdeep Mukherjee, Peter Schrammel

\*******************************************************************/


#include <langapi/language_util.h>
#include <util/find_symbols.h>
#include "acdl_solver.h"
#include "acdl_domain.h"
//#include "acdl_worklist_ordered.h"
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

property_checkert::resultt acdl_solvert::propagate(const local_SSAt &SSA)
{
  while (!worklist.empty())
  {
    const acdl_domaint::statementt statement = worklist.pop();
    
#ifdef DEBUG
    std::cout << "Pop: " << from_expr (SSA.ns, "", statement)
        << std::endl;
#endif

    // compute update of abstract value
    acdl_domaint::valuet v;
    acdl_domaint::valuet v1;
    acdl_domaint::deductionst deductions;
     
    implication_graph.to_value(v);
    // Do we need to normalize value here since 
    // this will remove all old decisions that are 
    // still stored in the implication graph. These 
    // old decisions can still contribute towards the 
    // future deductions called in domain operator() below
    //domain.normalize_val(v);

    // check if domain.normalize_val is correct
    /*domain.normalize_val(v1);
    // check if (v != v1) is UNSAT
    std::unique_ptr<incremental_solvert> solver(
      incremental_solvert::allocate(SSA.ns,true));
    not_equal_exprt eqexp(v,v1);
    *solver << eqexp;
    decision_proceduret::resultt result = (*solver)();
    assert(result == decision_proceduret::D_UNSATISFIABLE);
    */

#ifdef DEBUG
    std::cout << "Computing old abstract value of implication graph: " << std::endl;
    for(acdl_domaint::valuet::const_iterator it = v.begin();it != v.end(); ++it)
        std::cout << from_expr(SSA.ns, "", *it) << std::endl;
#endif    

#ifdef DEBUG
    std::cout << "Old: ";
    domain.output(std::cout, v) << std::endl;
#endif

    // select vars for projection
    acdl_domaint::varst project_vars;
    find_symbols(statement,project_vars);
    acdl_domaint::varst projected_live_vars;
    projected_live_vars = worklist.check_var_liveness(project_vars); 
    acdl_domaint::valuet new_v;
    domain(statement, projected_live_vars, v, new_v, deductions);
    
    // update implication graph
    implication_graph.add_deductions(SSA, deductions);
    
    // update worklist based on variables in the consequent (new_v)
    // - collect variables in new_v
    acdl_domaint::varst new_variables;
    for(acdl_domaint::valuet::const_iterator 
          it1 = new_v.begin(); it1 != new_v.end(); ++it1)
       find_symbols(*it1, new_variables);

      
      // - call worklist update
      worklist.update(SSA, new_variables, statement); 
    
#ifdef DEBUG
    std::cout << "New: ";
    domain.output(std::cout, new_v) << std::endl;
#endif

    // abstract value after meet is computed here
    // The abstract value of the implication 
    // graph gives the meet of new 
    // deductionst and old deductionst since
    // we are computing the gfp
    implication_graph.to_value(new_v);
    
    // TEST: meet is computed because we are doing gfp
    //domain.meet (new_v, v);
    //domain.normalize(v,projected_live_vars);

#ifdef DEBUG
    std::cout << "Computing new abstract value of implication graph: " << std::endl;
    for(acdl_domaint::valuet::const_iterator it = new_v.begin();it != new_v.end(); ++it)
        std::cout << from_expr(SSA.ns, "", *it) << std::endl;
#endif    

    //Cool! We got UNSAT
    // domain.normalize(new_v, projected_live_vars);
    domain.normalize(new_v);
    if(domain.is_bottom(new_v))
    {
#ifdef DEBUG
      std::cout << "Propagation finished with BOTTOM" << std::endl;
#endif
      // empty the worklist because the present decision 
      // lead to bottom, so all information in the 
      // worklist is irrelevant
      while(!worklist.empty()) 
       worklist.pop(); 
      // empty the live variables because the worklist 
      // items are no more relevent, hence the live variables
      // are no more relevant 
      worklist.live_variables.erase
      (worklist.live_variables.begin(), worklist.live_variables.end()); 
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

bool
acdl_solvert::decide (const local_SSAt &SSA)
{
  acdl_domaint::valuet v;
  implication_graph.to_value(v);
  domain.normalize_val(v);
  acdl_domaint::meet_irreduciblet dec_expr=decision_heuristics(SSA, v);
  // no new decisions can be made
  if(dec_expr == false_exprt())
    return false; 

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
  implication_graph.add_decision(dec_expr);

#if 0  
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
#endif
  
  // Take a meet of the decision expression (decision) with the current abstract state (v).
  // The new abstract state is now in v
#ifdef DEBUG
    std::cout << "FINAL DECISION: " << from_expr (SSA.ns, "", dec_expr) << std::endl;
    domain.meet(dec_expr,v);
    std::cout << "Before normalize: " << std::endl;
    domain.output(std::cout, v) << std::endl;
    domain.normalize_val(v);
    std::cout << "New: ";
    domain.output(std::cout, v) << std::endl;
#endif
  
  // access the decision statement associated with the chosen cond variables
  acdl_domaint::statementt dec_stmt = decision_heuristics.dec_statement;
  
  acdl_domaint::varst dec_vars;
  // find all symbols in the decision expression
  find_symbols(dec_stmt, dec_vars);

  // initialize the worklist here with all 
  // transitive dependencies of the decision
  //worklist.dec_update(SSA, dec_stmt);
  
  worklist.dec_update(SSA, dec_expr);

  return true;
}

/*******************************************************************

 Function: acdl_solvert::analyze_conflict()

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

property_checkert::resultt 
acdl_solvert::analyze_conflict(const local_SSAt &SSA)
{
  exprt learned_clause;
  property_checkert::resultt result = conflict_analysis(SSA, implication_graph, learned_clause);
  if(result == property_checkert::PASS) 
    return result;
  else {
    // store the learned clause
    learned_clauses.push_back(learned_clause);

    acdl_domaint::valuet v;
    implication_graph.to_value(v);
    domain.normalize_val(v);
    exprt dec_expr = implication_graph.dec_trail.back();

    //exprt dec_expr = cond_dec_heuristic.dec_trail.back();
    domain.meet(dec_expr,v);
#ifdef DEBUG
    std::cout << "New [Analyze conflict]: ";
    domain.output(std::cout, v) << std::endl;
#endif


    // TODO: Push all learnt clauses 
    // in to the worklist


    acdl_domaint::varst dec_vars;
    // find all symbols in the decision expression
    find_symbols(dec_expr, dec_vars);
    // update the worklist based on all transitively dependant elements of the
    // learnt clause 
    worklist.dec_update(SSA, dec_expr);
    // pop from the decision trail 
    //cond_dec_heuristic.dec_trail.pop_back();
    implication_graph.dec_trail.pop_back();
    result = propagate(SSA);
    return result;
  }
#if 0  
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

#endif 
}


/*******************************************************************

 Function: acdl_solvert::init()

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/
/*void acdl_solvert::init() 
{
  std::string heur = options.get_option("dec-heur");

  if(heur == "berkmin") 
    dec_heur = BERKMIN;
  else if(heur == "range")
    dec_heur = RANGE;
  else if(heur == "range-rel")
    dec_heur = RANGE_REL;
  else if(heur == "rand")
    dec_heur = RAND;
  else 
    dec_heur = RAND; //DEFAULT
}
*/

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
  //init();
  worklist.initialize(SSA);
  // call initialize live variables
  worklist.initialize_live_variables();
  std::set<exprt> decision_variable;
  // initialize the decision variables
  // Note that the decision variable contains
  // variables only in the slicing, that is, 
  // related to the property
  decision_variable.insert(worklist.worklist_vars.begin(), worklist.worklist_vars.end());

  // do not insert guard and phi 
  // variables in the decision variables
  std::string str1("guard");
  std::string str2("#phi");
  std::string name;
  for(std::set<exprt>::const_iterator 
    it = decision_variable.begin(); 
    it != decision_variable.end(); ++it)
  {
    const irep_idt &identifier = it->get(ID_identifier);
    name = id2string(identifier);
    std::size_t found1 = name.find(str1);
    std::size_t found2 = name.find(str2);
    if (found1==std::string::npos && found2==std::string::npos) {
      decision_heuristics.decision_variables.insert(*it);
    }
  } 
   
#ifdef DEBUG
  std::cout << "Printing all decision variables inside solver" << std::endl;
  for(std::set<exprt>::const_iterator 
    it = decision_heuristics.decision_variables.begin(); 
    it != decision_heuristics.decision_variables.end(); ++it)
      std::cout << from_expr(SSA.ns, "", *it) << "  ," << std::endl;
#endif
  // collect variables for completeness check
  std::set<symbol_exprt> all_vars;
  all_vars = worklist.live_variables; 
  /*for (local_SSAt::nodest::const_iterator n_it = SSA.nodes.begin ();
      n_it != SSA.nodes.end (); ++n_it)
  {
    for (local_SSAt::nodet::equalitiest::const_iterator it =
        n_it->equalities.begin (); it != n_it->equalities.end (); ++it)
      find_symbols (*it, all_vars);
    for (local_SSAt::nodet::constraintst::const_iterator it =
        n_it->constraints.begin (); it != n_it->constraints.end (); ++it)
      find_symbols (*it, all_vars);
    for (local_SSAt::nodet::assertionst::const_iterator it =
        n_it->assertions.begin (); it != n_it->assertions.end (); ++it)
      find_symbols (*it, all_vars);
  }*/

  implication_graph.clear(); //set to top
  acdl_domaint::valuet v;
  implication_graph.to_value(v);
  domain.normalize_val(v);
  // check if abstract value v of the 
  // implication graph is top for the first time 
  // because ACDL starts with TOP
  assert(domain.is_top(v)); 

  property_checkert::resultt result = property_checkert::UNKNOWN;
  while(result == property_checkert::UNKNOWN)
  {
    while(true)
    {
      // deduction phase in acdl
      std::cout << "********************************" << std::endl;
      std::cout << "        DEDUCTION PHASE " << std::endl;
      std::cout << "********************************" << std::endl;
      result = propagate(SSA);

      std::cout << "****************************************************" << std::endl;
      std::cout << " IMPLICATION GRAPH AFTER DEDUCTION PHASE" << std::endl;
      std::cout << "****************************************************" << std::endl;
      implication_graph.print_graph_output(SSA);
      // check for conflict
      if(result == property_checkert::PASS) //UNSAT
        break;
    
      // check for satisfying assignment
      acdl_domaint::valuet v;
      implication_graph.to_value(v);
      domain.normalize_val(v);
      if(domain.is_complete(v, all_vars))
        return property_checkert::FAIL;
      
      std::cout << "********************************" << std::endl;
      std::cout << "         DECISION PHASE"          << std::endl;
      std::cout << "********************************" << std::endl;
      // make a decision
      bool status = decide(SSA);
      if(!status) {
        std::cout << "Failed to verify program" << std::endl;
#ifdef DEBUG
    std::cout << "Minimal unsafe element is" << std::endl;
    for(acdl_domaint::valuet::const_iterator it = v.begin();it != v.end(); ++it)
        std::cout << from_expr(SSA.ns, "", *it) << std::endl;
#endif    
        break;
      }
      std::cout << "****************************************************" << std::endl;
      std::cout << "IMPLICATION GRAPH AFTER DECISION PHASE" << std::endl;
      std::cout << "****************************************************" << std::endl;
      implication_graph.print_graph_output(SSA);
    }

    std::cout << "********************************" << std::endl;
    std::cout << "    CONFLICT ANALYSIS PHASE" << std::endl;
    std::cout << "********************************" << std::endl;

    // analyze conflict ...
    result = analyze_conflict(SSA);
    // decision level 0 conflict
    if(result == property_checkert::PASS) //UNSAT
      break;
  }

  return result;
}
