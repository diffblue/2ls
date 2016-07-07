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



/*******************************************************************

 Function: acdl_solvert::deduce()

 Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
bool acdl_solvert::deduce(const local_SSAt &SSA, const exprt &assertion)
{
    assert(analyzes_conflict.learned_clauses.size() != 0);
    acdl_domaint::valuet v;
    int conf_lit = -1; 
    analyzes_conflict.conflicting_clause = -1;
    conflict_graph.to_value(v);
    
    int size_val=v.size();
    int i=0;
    // TODO: smart way is to check (*solver << conjunction(clause[i],expr) == UNSAT)
    while(i < analyzes_conflict.learned_clauses.size()) {
      acdl_domaint::valuet clause_val = analyzes_conflict.learned_clauses[i];
      int sizet = clause_val.size();
      for(int k=0; k<sizet; k++) {
       exprt exp1 = clause_val[k];
       // check for each value in abstract value "v"
       for(int j=0;i<size_val;j++) {
        exprt exp2 = v[j];
        if(domain.compare(exp1, exp2)==1)
          conf_lit = k;
       }
      }
      if(conf_lit == -1) {
        // this means that the clause is conflicting
        // since all the literals in the clause are contradicting
        analyzes_conflict.conflicting_clause = i;
        // PROPOSITIONAL proof
        analyzes_conflict.last_proof = analyzes_conflict.PROPOSITIONAL;
        return true;
        break;
      } 
    }
    return false;
}

/*******************************************************************\

Function: acdl_solvert::propagation

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

property_checkert::resultt acdl_solvert::propagation(const local_SSAt &SSA, const exprt &assertion)
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
     
    conflict_graph.to_value(v);
    // Do we need to normalize value here since 
    // this will remove all old decisions that are 
    // still stored in the implication graph. These 
    // old decisions can still contribute towards the 
    // future deductions called in domain operator() below
    //domain.normalize_val(v);

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
    //implication_graph.add_deductions(SSA, deductions);
    conflict_graph.add_deductions(SSA, deductions);
    
    // update worklist based on variables in the consequent (new_v)
    // - collect variables in new_v
    acdl_domaint::varst new_variables;
    for(acdl_domaint::valuet::const_iterator 
          it1 = new_v.begin(); it1 != new_v.end(); ++it1)
       find_symbols(*it1, new_variables);

      
      // - call worklist update
      worklist.update(SSA, new_variables, statement, assertion); 
    
#ifdef DEBUG
    std::cout << "New: ";
    domain.output(std::cout, new_v) << std::endl;
#endif

    // abstract value after meet is computed here
    // The abstract value of the implication 
    // graph gives the meet of new 
    // deductionst and old deductionst since
    // we are computing the gfp
    //implication_graph.to_value(new_v);
    conflict_graph.to_value(new_v);
    
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
      // Abstract Interpretation proof
      analyzes_conflict.last_proof = analyzes_conflict.ABSINT;
      return property_checkert::PASS; //potential UNSAT (modulo decisions)
    }
  }

#ifdef DEBUG
  std::cout << "Propagation finished with UNKNOWN" << std::endl;
#endif
  
  return property_checkert::UNKNOWN;
}

/*******************************************************************

 Function: acdl_solvert::propagate()

 Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
property_checkert::resultt acdl_solvert::propagate
    (const local_SSAt &SSA, const exprt &assertion)
{
  if(analyzes_conflict.learned_clauses.size() == 0)
   return propagation(SSA, assertion);
  else {
   // check if the conflict is due to learnt clauses
   bool conflict = deduce(SSA, assertion);
   // PROPOSITIONAL proof
   analyzes_conflict.last_proof = analyzes_conflict.PROPOSITIONAL;
   if(!conflict)
    return propagation(SSA, assertion);
  }
}

/*******************************************************************

 Function: acdl_solvert::decide()

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

bool
acdl_solvert::decide (const local_SSAt &SSA, const exprt& assertion)
{
  acdl_domaint::valuet v;
  //implication_graph.to_value(v);
  conflict_graph.to_value(v);
    
  domain.normalize_val(v);
  // the decision must know about the learned clause as well
  // so that it can not make wrong decisions on the variables which 
  // is already singleton in the learned clause, for example 
  // learned_clause=!cond21, new_decision=cond21 -- which contradicts
  unsigned i = 0;
  if(analyzes_conflict.learned_clauses.size() > 0) {
    while(i < analyzes_conflict.learned_clauses.size()) {
      acdl_domaint::valuet clause_val = analyzes_conflict.learned_clauses[i];
      const exprt &clause_expr = conjunction(clause_val);
      v.push_back(clause_expr);
      i++;
    } 
  }
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
  // implication_graph.add_decision(dec_expr);
  conflict_graph.add_decision(dec_expr);

  // check that the meet_ireducibles in the prop trail 
  // is consistent after adding every decision. The value 
  // should not lead to UNSAT 
  // (that is, there must not be x>0, x<0
  // at the same time in the trail)
  acdl_domaint::valuet new_value;
  conflict_graph.to_value(new_value);
  assert(domain.check_val_consistency(new_value));

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
  
  worklist.dec_update(SSA, dec_expr, assertion);

  return true;
}

/*******************************************************************

 Function: acdl_solvert::analyze_conflict()

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/
bool acdl_solvert::analyze_conflict(const local_SSAt &SSA, const exprt& assertion) 
{
 acdl_domaint::valuet learned_clause;
 if(!analyzes_conflict(SSA, conflict_graph)) {
   return false;
 }
 else {    
    if(analyzes_conflict.disable_backjumping) {
      acdl_domaint::valuet v;
      conflict_graph.to_value(v);
      // call normalize or normalize_val ? 
      domain.normalize_val(v);
      exprt dec_expr = conflict_graph.prop_trail.back();
      domain.meet(dec_expr,v);
#ifdef DEBUG
      std::cout << "New [Analyze conflict]: ";
      domain.output(std::cout, v) << std::endl;
#endif

      acdl_domaint::varst dec_vars;
      // find all symbols in the decision expression
      find_symbols(dec_expr, dec_vars);
      // update the worklist based on all transitively dependant elements of the learnt clause 
      worklist.dec_update(SSA, dec_expr, assertion);
      return true;
    }
    else {
      acdl_domaint::valuet v;
      conflict_graph.to_value(v);
      // call normalize or normalize_val ? 
      domain.normalize_val(v);

      domain.meet(learned_clause,v);
      // store the learned clause
      // analyzes_conflict.learned_clauses.push_back(learned_clause);
      
      // iterate over all learned clause and normalize them 
      // for example- learnt-clause1: (x<=0 && y>=2)
      // learnt-clause2: (y>=2 && x<=5)
      // Normalized learned clause: (x<=0 && y>=2) 
      unsigned j=0,k=0;
      acdl_domaint::valuet normalize_learned_clause;
      while(j < analyzes_conflict.learned_clauses.size()) {
        k=0;
        acdl_domaint::valuet learned_val = analyzes_conflict.learned_clauses[j];
        while(k < learned_val.size()) {
          // check for duplicate
          acdl_domaint::valuet::iterator it;  
          it = find(normalize_learned_clause.begin(), normalize_learned_clause.end(), learned_val[k]);
          if(it == normalize_learned_clause.end())
            normalize_learned_clause.push_back(learned_val[k]);
          k++;
        }
        j++;
      }

      // insert the normalized learned clause in to the worklist
      domain.normalize_val(normalize_learned_clause);
      const exprt &clause_expr = conjunction(normalize_learned_clause);
      worklist.push(clause_expr);
   
   #if 0   
      // iterate over learned clauses and convert
      // them to exprt. Insert these exprts to worklist
      unsigned i=0;
      while(i < learned_clauses.size()) {
        std::cout << "Pushing learned clause into the worklist" << std::endl;
        acdl_domaint::valuet clause_val = learned_clauses[i];
        const exprt &clause_expr = conjunction(clause_val);
        worklist.push(clause_expr);
        i++;
      }
    #endif  
       
      acdl_domaint::varst learn_vars;
      const exprt learned_expr = conjunction(learned_clause);
      acdl_domaint::statementt learned_stmt = learned_expr;
      // find all symbols in the decision expression
      find_symbols(learned_stmt, learn_vars);
      // update the worklist based on all transitively dependant elements of the
      // learnt clause 
       
      worklist.dec_update(SSA, learned_stmt, assertion);
      return true;
    }
  }


#if 0 // working with implication graph
 if(!conflict_analysis(SSA, implication_graph, learned_clause))
   return false;
 else {    
    if(conflict_analysis.disable_backjumping) {
      acdl_domaint::valuet v;
      implication_graph.to_value(v);
      // call normalize or normalize_val ? 
      domain.normalize_val(v);
      exprt dec_expr = implication_graph.dec_trail.back();

      domain.meet(dec_expr,v);
#ifdef DEBUG
      std::cout << "New [Analyze conflict]: ";
      domain.output(std::cout, v) << std::endl;
#endif

      acdl_domaint::varst dec_vars;
      // find all symbols in the decision expression
      find_symbols(dec_expr, dec_vars);
      // update the worklist based on all transitively dependant elements of the learnt clause 
      worklist.dec_update(SSA, dec_expr, assertion);
      // pop from the decision trail 
      // implication_graph.dec_trail.pop_back();
      return true;
    }
    else {
      acdl_domaint::valuet v;
      implication_graph.to_value(v);
      // call normalize or normalize_val ? 
      domain.normalize_val(v);

      domain.meet(learned_clause,v);
      // store the learned clause
      learned_clauses.push_back(learned_clause);
      
      // iterate over all learned clause and normalize them 
      // for example- learnt-clause1: (x<=0 && y>=2)
      // learnt-clause2: (y>=2 && x<=5)
      // Normalized learned clause: (x<=0 && y>=2) 
      unsigned j=0,k=0;
      acdl_domaint::valuet normalize_learned_clause;
      while(j < learned_clauses.size()) {
        k=0;
        acdl_domaint::valuet learned_val = learned_clauses[j];
        while(k < learned_val.size()) {
          // check for duplicate
          acdl_domaint::valuet::iterator it;  
          it = find(normalize_learned_clause.begin(), normalize_learned_clause.end(), learned_val[k]);
          if(it == normalize_learned_clause.end())
            normalize_learned_clause.push_back(learned_val[k]);
          k++;
        }
        j++;
      }

      // insert the normalized learned clause in to the worklist
      domain.normalize_val(normalize_learned_clause);
      const exprt &clause_expr = conjunction(normalize_learned_clause);
      worklist.push(clause_expr);
   
   #if 0   
      // iterate over learned clauses and convert
      // them to exprt. Insert these exprts to worklist
      unsigned i=0;
      while(i < learned_clauses.size()) {
        std::cout << "Pushing learned clause into the worklist" << std::endl;
        acdl_domaint::valuet clause_val = learned_clauses[i];
        const exprt &clause_expr = conjunction(clause_val);
        worklist.push(clause_expr);
        i++;
      }
    #endif  
       
      acdl_domaint::varst learn_vars;
      const exprt learned_expr = conjunction(learned_clause);
      acdl_domaint::statementt learned_stmt = learned_expr;
      // find all symbols in the decision expression
      find_symbols(learned_stmt, learn_vars);
      // update the worklist based on all transitively dependant elements of the
      // learnt clause 
       
      worklist.dec_update(SSA, learned_stmt, assertion);
      return true;
    }
  }

#endif // working above code with graph

  #if 0
  // the conflict analysis returns PASS/FAIL/UNKNOWN
  exprt learned_clause;
  property_checkert::resultt result = conflict_analysis(SSA, implication_graph, learned_clause);
  if(result == property_checkert::PASS) 
    return result;
  else {
    // store the learned clause
    learned_clauses.push_back(learned_clause);

    acdl_domaint::valuet v;
    implication_graph.to_value(v);
    // call normalize or normalize_val ? 
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
    worklist.dec_update(SSA, dec_expr, assertion);
    // pop from the decision trail 
    //cond_dec_heuristic.dec_trail.pop_back();
    implication_graph.dec_trail.pop_back();
    result = propagate(SSA, assertion);
    return result;
  }
  #endif

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
void acdl_solvert::init()
{
  // iterate over all vars
  for(std::set<symbol_exprt>::iterator it = all_vars.begin();
    it!=all_vars.end();it++)
  {
    //number all symbol_exprts
    unsigned nr = conflict_graph.numbering_symbol.number(to_symbol_expr(*it));
    assert(nr == conflict_graph.values.size());   
    std::pair<int, int> intv;
    intv.first = -99999;
    intv.second = -99999;
    conflict_graph.values.push_back(intv); 
  }
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

property_checkert::resultt acdl_solvert::operator()(
  const local_SSAt &SSA,
  const exprt &assertion,
  const exprt &additional_constraint)
{
  // pass additional constraint and the assertions to the worklist
  worklist.initialize(SSA, assertion, additional_constraint);
  
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
  std::string str3("#lb");
  std::string name;
  for(std::set<exprt>::const_iterator 
    it = decision_variable.begin(); 
    it != decision_variable.end(); ++it)
  {
    const irep_idt &identifier = it->get(ID_identifier);
    name = id2string(identifier);
    std::size_t found1 = name.find(str1);
    std::size_t found2 = name.find(str2);
    std::size_t found3 = name.find(str3);
    if (found1==std::string::npos && found2==std::string::npos && found3==std::string::npos) {
      decision_heuristics.initialize_dec_variables(*it);
    }
  } 

#ifdef DEBUG
  std::cout << "Printing all decision variables inside solver" << std::endl;
  for(std::set<exprt>::const_iterator 
    it = decision_heuristics.decision_variables.begin(); 
    it != decision_heuristics.decision_variables.end(); ++it)
     std::cout << from_expr(SSA.ns, "", *it) << "  ," << std::endl;

  std::cout << "The additional constraint for the loop is: " << from_expr(SSA.ns, "", additional_constraint) << std::endl;
#endif
  // collect variables for completeness check
  all_vars = worklist.live_variables; 
  
  // initialize values trail
  init();

  conflict_graph.init();
  acdl_domaint::valuet v;
  conflict_graph.to_value(v);
  domain.normalize_val(v);
  // check if abstract value v of the 
  // implication graph is top for the first time 
  // because ACDL starts with TOP
  assert(domain.is_top(v)); 
  
  unsigned iteration = 0;

  property_checkert::resultt result = property_checkert::UNKNOWN;
  // the result is already decided for programs
  // which can be solved only using deductions  
  result = propagate(SSA, assertion);
  
  std::cout << "****************************************************" << std::endl;
  std::cout << " IMPLICATION GRAPH AFTER DEDUCTION PHASE" << std::endl;
  std::cout << "****************************************************" << std::endl;
  conflict_graph.dump_trail(SSA);
  
  bool complete=false;
  // if result = UNSAT, then the proof is complete 
  if(result == property_checkert::PASS)
    return result; 
  // if result = UNKNOWN or FAIL, 
  // then check for completeness
  else {
    // check for satisfying assignment
    acdl_domaint::valuet val;
    //implication_graph.to_value(val);
    conflict_graph.to_value(val);
    domain.normalize_val(val);
    if(domain.is_complete(val, all_vars)) {
      complete = true;
      return property_checkert::FAIL;
    }
  }
     
  while(true)
  {
    // check the iteration bound
    if(ITERATION_LIMIT >= 0 && iteration > ITERATION_LIMIT) {
#ifdef DEBUG
      std::cout << "Iteration limit reached" << std::endl; 
#endif
      break;
    }

    std::cout << std::endl 
      << "  ITERATION (decision):: " << iteration++ << std::endl
      << "================================" << std::endl;
    std::cout << "********************************" << std::endl;
    std::cout << "         DECISION PHASE"          << std::endl;
    std::cout << "********************************" << std::endl;
    // make a decision
    bool status = decide(SSA, assertion);

    if(!status) {
      // if the abstract value is complete and 
      // no more decisions can be made, then 
      // there is a counterexample. Return result=FAILED. 
      if (complete) 
        return result;
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
    conflict_graph.dump_trail(SSA);

    // deduction phase in acdl
    std::cout << "********************************" << std::endl;
    std::cout << "        DEDUCTION PHASE " << std::endl;
    std::cout << "********************************" << std::endl;
    result = propagate(SSA, assertion);

    std::cout << "****************************************************" << std::endl;
    std::cout << " IMPLICATION GRAPH AFTER DEDUCTION PHASE" << std::endl;
    std::cout << "****************************************************" << std::endl;
    conflict_graph.dump_trail(SSA);
    // completeness check is done when 
    // result=UNKNOWN or result=FAIL
    if (result == property_checkert::UNKNOWN || 
        result == property_checkert::FAIL) 
    {
      // check for satisfying assignment
      acdl_domaint::valuet v;
      conflict_graph.to_value(v);
      // Do we call normalize_val here ? !!
      domain.normalize_val(v);
     
      // successful execution of is_complete check 
      // ensures that all variables are singletons
      // But we invoke another decision phase
      // to infer that "no more decisions can be made"
      if(domain.is_complete(v, all_vars)) {
        // set complete flag to TRUE
        complete = true;
        result = property_checkert::FAIL;
      }
    }
    else {
      std::cout << "SUCCESSFULLY PROVEN CASE" << std::endl;
      // check for conflict
      do 
      {
        // call generalize_proof here
        // generalize_proof();

        std::cout << "********************************" << std::endl;
        std::cout << "    CONFLICT ANALYSIS PHASE" << std::endl;
        std::cout << "********************************" << std::endl;
        // analyze conflict ...
        if(!analyze_conflict(SSA, assertion)) {
          std::cout << "No further backtrack possible " << std::endl;
#ifdef DEBUG
          unsigned i=0;
          if(analyzes_conflict.learned_clauses.size() > 0) {
            std::cout << "The final set of learned clauses are:" << std::endl;
            while(i < analyzes_conflict.learned_clauses.size()) {
              acdl_domaint::valuet clause_val = analyzes_conflict.learned_clauses[i];
              const exprt &clause_expr = conjunction(clause_val);
              std::cout << "clause " << i << "is: " << from_expr(SSA.ns, "", clause_expr) << std::endl;
              i++;
            }
          }
#endif
          goto END; // result = PASS when it breaks for here
        }
        // deduction phase in acdl
        std::cout << "********************************" << std::endl;
        std::cout << "        DEDUCTION PHASE " << std::endl;
        std::cout << "********************************" << std::endl;
        result = propagate(SSA, assertion);

        std::cout << "****************************************************" << std::endl;
        std::cout << " IMPLICATION GRAPH AFTER DEDUCTION PHASE" << std::endl;
        std::cout << "****************************************************" << std::endl;
        conflict_graph.dump_trail(SSA);


      } while(result == property_checkert::PASS); //UNSAT
    }
  } // end of while(true)
  END:
  std::cout << "Procedure terminated after iteration: "  << iteration  << std::endl;
  // return result;
}
