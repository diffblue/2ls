/*******************************************************************\

Module: ACDL Clause Learning Base

Author: Rajdeep Mukherjee, Peter Schrammel

\*******************************************************************/

#include <util/find_symbols.h>
#include "acdl_analyze_conflict_base.h"

//#define DEBUG

/*******************************************************************\

Function: abstr_dpll_searcht::chronological_backtrack
 
  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
bool acdl_analyze_conflict_baset::chronological_backtrack(const local_SSAt &SSA, acdl_conflict_grapht &graph)
{
#ifdef DEBUG
  std::cout << "inside backtrack" << std::endl;
#endif  
  if(graph.current_level == 0) {
    backtrack_level = -1; // no further backtrack possible
    return false;
  }
   
  unsigned first_idx = graph.control_trail.back();

#ifdef DEBUG  
  std::cout << "val_trail size is: " << graph.val_trail.size() << "control_trail.back is: "  << first_idx << std::endl;
#endif  
  assert(graph.val_trail.size() >= first_idx + 1);
  exprt dec_exp = graph.prop_trail[first_idx];
 
  // check val_trail and prop_trail are of equal size
  assert(graph.prop_trail.size() == graph.val_trail.size());
   
#ifdef DEBUG  
  std::cout << "The decision to be flipped is " << from_expr(SSA.ns, "", dec_exp);
  std::cout << "The trail before  backtracking is" << std::endl;
#endif  
  graph.dump_trail(SSA);

  // backtrack one level
  cancel_once(SSA, graph);
  
  // flip the expression
  exprt exp = flip(dec_exp);

  graph.assign_to_trail(exp);

#ifdef DEBUG
  std::cout << "The trail after backtracking and assigning negation of previous decision is" << std::endl;
#endif  
  graph.dump_trail(SSA);
  
  // check val_trail and prop_trail are of 
  // equal size after backtracking
  assert(graph.prop_trail.size() == graph.val_trail.size());
  
  // update the backtrack level
  backtrack_level = graph.current_level;
  
  just_backtracked = true;
  
  graph.check_consistency();

  return true;
}

/*******************************************************************\

Function: acdl_analyze_conflict_baset::operator()

  Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/
bool acdl_analyze_conflict_baset::operator() (const local_SSAt &SSA, acdl_conflict_grapht &graph)
{
  if(disable_backjumping) {
   return(chronological_backtrack(SSA, graph)); 
  }
  
  acdl_domaint::valuet conf_clause;
  get_conflict_clause(SSA, graph, conf_clause);
 
  // no further backtrack possible
  if(backtrack_level < 0) {
    return false;
  }
  
#ifdef DEBUG  
  std::cout << "Decision trail before backtracking" << std::endl;
#endif  
  graph.dump_dec_trail(SSA); 
  
  // print the conflict clause
#ifdef DEBUG  
  std::cout << "Unnormalized Learnt Clause is " << from_expr(SSA.ns, "", disjunction(conf_clause)) << std::endl;
#endif  

  // [TEMPORARY USE] save the 
  // present decision level before backtracking
  int present_dl = graph.current_level;
  // save the last decision before backtracking
  exprt dec_expr = graph.dec_trail.back();
  
  // backtrack
  std::cout << "****************" << std::endl;
  std::cout << "BACKTRACK PHASE" << std::endl;
  std::cout << "****************" << std::endl;
#ifdef DEBUG
  std::cout << "backtrack to dlevel: " << backtrack_level << std::endl;
#endif  
  cancel_until(SSA,graph,backtrack_level);
#ifdef DEBUG  
  std::cout << "Trail after backtracking" << std::endl;
  graph.dump_trail(SSA); 
#endif  
  
#ifdef DEBUG  
  std::cout << "Decision trail after backtracking" << std::endl;
  graph.dump_dec_trail(SSA); 
#endif  
  
  backtracks++;
  
  /* 
  Steps to follow for application of unit rule to learnt clause:
  -- Step 1: Construct the learnt clause
  -- Step 2: Normalize the learnt clause without UIP
  -- Step 3: Normalize the current partial assignment
  -- Step 4: The learnt clause should be UNIT !
  */
  // The above steps holds true for 
  // monotonic and non-monotonic decision
  // Note that the learnt clause can have redundant
  // literals, so normalize the learnt clause without UIP
  // The normalisation steps guarantee the following
  //  -- leads to shorter clause
  //  -- normalisation is equivalent transformation 
  //  -- backtrack level is unaffected by normalisation
  //  -- unit rule must hold after normalisation  
  
  
  // -- Step 2: Normalize the learnt clause without UIP
  // Note that the last element of the 
  // learnt clause is the UIP
  acdl_domaint::valuet norm_conf_clause;
  for(unsigned i=0;i<conf_clause.size()-1;i++)
     norm_conf_clause.push_back(conf_clause[i]);         
  domain.normalize(norm_conf_clause);
  // now push the uip into the learnt clause
  norm_conf_clause.push_back(conf_clause.back());         

  // add the conflict clause to the learned clause database
#ifdef DEBUG  
  std::cout << "Normalized Learnt Clause is " << from_expr(SSA.ns, "", disjunction(norm_conf_clause)) << std::endl;
#endif  
  learned_clauses.push_back(norm_conf_clause);
  
  exprt unit_lit;
  acdl_domaint::valuet v;
  graph.to_value(v);
  // check that the clause is unit,
  // this causes one propagation because
  // the clause is unit
  int result = domain.unit_rule(SSA, v, norm_conf_clause, unit_lit);
 
  // the learned clause must be asserting
  assert(result == domain.UNIT);
  
  // push the new deductions from unit_rule 
  // to the conflict graph explicitly
  // [NOTE] the conflict_analysis is followed
  // by deductions on learned clause where same
  // deduction may happen, but we push the deductions
  // in the graph here because the following 
  // deduction should return SATISFIABLE and 
  // does not yield that the same deduction 
  graph.assign(unit_lit);

  // the prop_trail is never emptied because it always
  // contains elements from first deduction which is 
  // agnostic to any decisions, hence the elements of 
  // first deduction are always consistent
  assert(graph.prop_trail.size() - graph.control_trail.size() >= 2);
  
  just_backtracked = true;
#ifdef DEBUG
  std::cout << "Successfully backtracked" << std::endl;
#endif
  
  // check graph consistency
  graph.check_consistency();
  return true;  
}


/*******************************************************************\

Function: acdl_analyze_conflict_baset::get_conflict_clause()

  Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/
 
void acdl_analyze_conflict_baset::get_conflict_clause
  (const local_SSAt &SSA, acdl_conflict_grapht &graph, acdl_domaint::valuet &conf_clause)
{
   // PROPOSITIONAL proof
   if(last_proof == PROPOSITIONAL) {
     assert(conflicting_clause != -1);     
     conf_clause = learned_clauses[conflicting_clause];
#ifdef DEBUG  
     std::cout << "Conflict is purely Propositional" << std::endl;
#endif     
   }
   // conflict is caused by Abstract Interpretation proof
   else if(last_proof == ABSINT) {
     acdl_domaint::valuet reason;
     get_ai_reason(SSA, graph, reason);
     // print the reason
#ifdef DEBUG  
     std::cout << "Reason: " << from_expr(SSA.ns, "", disjunction(reason)) << std::endl;
#endif     

     for(acdl_domaint::valuet::iterator it = reason.begin();
          it != reason.end(); it++)
     {
       negate(*it, conf_clause);
     } 
#ifdef DEBUG  
     std::cout << "Conflict is purely from Abstract Interpretation Proof" << std::endl;
#endif     
   }

#ifdef DEBUG  
  std::cout << "Conflict at decision level is " << graph.current_level  <<std::endl;
#endif  
   if(conf_clause.size() == 0)
     backtrack_level = -1;
   else 
     find_uip(SSA, graph, conf_clause, graph.current_level);
  
  // print the conflict clause
#ifdef DEBUG  
  std::cout << "learnt clause: " << from_expr(SSA.ns, "", disjunction(conf_clause)) << std::endl;
#endif  
}

/*******************************************************************\

Function: acdl_analyze_conflict_baset::cancel_until()

  Inputs:

 Outputs:

 Purpose: backtracks by several level

 \*******************************************************************/
void acdl_analyze_conflict_baset::cancel_until
   (const local_SSAt &SSA, acdl_conflict_grapht &graph, int lvl) 
{
  while(graph.current_level > lvl) {
     // dl0 corresponds to deductions
     // which are always consistent, so 
     // do not cancel elements from dl0
     //if(graph.current_level == 0) return;
     cancel_once(SSA,graph);
  }
}

/*******************************************************************\

Function: acdl_analyze_conflict_baset::cancel_once()

  Inputs:

 Outputs:

 Purpose: backtracks by one level

\*******************************************************************/
void acdl_analyze_conflict_baset::cancel_once(const local_SSAt &SSA, acdl_conflict_grapht &graph) 
{
  while(graph.prop_trail.size() > graph.control_trail.back()) 
  {
    graph.val_trail.pop_back();
    graph.prop_trail.pop_back();
  } 
  
  graph.control_trail.pop_back();
  bcp_queue_top=graph.prop_trail.size();
  graph.dec_trail.pop_back();
  graph.current_level--;
}

/*******************************************************************\

Function: acdl_analyze_conflict_baset::flip()

  Inputs:

 Outputs:

 Purpose: flip present meet irreducible

\*******************************************************************/
exprt acdl_analyze_conflict_baset::flip(acdl_domaint::meet_irreduciblet &m) 
{
  not_exprt not_exp(m); 
  return not_exp;
}
  
/*******************************************************************\

Function: acdl_analyze_conflict_baset::negate()

  Inputs:

 Outputs:

 Purpose: negate the meet irreducible and push into reason 

\*******************************************************************/
   
void acdl_analyze_conflict_baset::negate
  (exprt& exp, acdl_domaint::valuet &clause)
{
  clause.push_back(flip(exp));  
}

/*******************************************************************\

Function: acdl_analyze_conflict_baset::get_ai_reason()

  Inputs:

 Outputs:

 Purpose: Get the recent value of decision variables from the prop trail 

\*******************************************************************/
 
void acdl_analyze_conflict_baset::get_ai_reason(const local_SSAt &SSA, 
              acdl_conflict_grapht &graph, acdl_domaint::valuet &reason)
{
  #if 0
  // collect all propagations in the reason 
  // upto the point where first decision was made 
  // iterate upto trail_size-2 since the last node 
  // is a FALSE node 
  int control_point = graph.control_trail[0];
  for(unsigned i=control_point;i<graph.prop_trail.size()-2;i++)
  {
    exprt prop_exp = graph.prop_trail[i];
    reason.push_back(prop_exp);
  }
  #endif
  
  // just take all decisions as reason
  for(unsigned i=0;i<graph.dec_trail.size();i++)
  {
    exprt dec_exp = graph.dec_trail[i];
    reason.push_back(dec_exp);
  }
  // now normalize the reason since there may be 
  // lot of redundant decisions 
  // domain.normalize(reason);

#if 0
  // Step 1: collect all decision variables by traversing the decision trail
  // (decisions follow the templates x<=0, y>10)
  // Step 2: traverse the prop_trail from back and collect the meet 
  // irreducibles involving these variables 
  // Step 3: Store these meet irreducibles from step 2 in reason
  
  acdl_domaint::varst dec_symbols;
  for(unsigned i=0;i<graph.dec_trail.size();i++)
  {
    exprt dec_exp = graph.dec_trail[i];
    acdl_domaint::varst symbols;
    find_symbols(dec_exp,symbols);
    dec_symbols.insert(symbols.begin(),symbols.end());
  }
#ifdef DEBUG
  std::cout << "Print all decision symbols so far: " << std::endl;
  for(acdl_domaint::varst::iterator it = dec_symbols.begin(); it != dec_symbols.end(); it++)
    std::cout << *it << std::endl;
#endif    
  
  int control_point = graph.control_trail.back(); 
  // traverse from the back of prop_trail to 
  // get the latest value, retrieve latest values
  // from only this deduction stage
  for(unsigned j=graph.prop_trail.size()-1;j>control_point;j--)
  {
    exprt prop_exp = graph.prop_trail[j];
    acdl_domaint::varst prop_symbols;
    // get symbols from this meet irreducible
    find_symbols(prop_exp, prop_symbols);
    // check if this symbol is in dec_symbols  
    for(acdl_domaint::varst::iterator it = prop_symbols.begin(); it != prop_symbols.end(); it++)
    {
      bool is_in = dec_symbols.find(*it) != dec_symbols.end();
      if(is_in) { 
        reason.push_back(prop_exp);
        break;
      }
    }   
  }
#endif
}
   
/*******************************************************************\

Function: acdl_analyze_conflict_baset::find_uip

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
  
void acdl_analyze_conflict_baset::find_uip(const local_SSAt &SSA, 
acdl_conflict_grapht &graph, acdl_domaint::valuet &result_clause, unsigned dlevel)
{
  assert(result_clause.size() != 0);
#ifdef DEBUG
  std::cout << "searching for uip" << std::endl;
#endif 

  if(dlevel == 0)
  { 
#ifdef DEBUG  
    std::cout << "Trying to resolve a conflict at dlevel 0" << std::endl;
#endif    
    backtrack_level = -1; //UNSAT
    return;
  }

  acdl_domaint::valuet target_level_lits;
  int max_reason_dl = -1;
  acdl_domaint::valuet new_result_clause;

  int clause_size=result_clause.size();

  unsigned contr_dl = 0;
  for(acdl_domaint::valuet::iterator it = result_clause.begin(); 
      it != result_clause.end(); ++it)
  {
    contr_dl = get_earliest_contradiction(SSA, graph, *it);
#ifdef DEBUG  
    std::cout << "The contradicted decision level is " << contr_dl << std::endl;
#endif    
    assert(contr_dl <= dlevel);
#ifdef DEBUG  
    std::cout << "Comparing max_dl " << max_reason_dl << "contr_dl " << contr_dl << std::endl;
#endif     
    if(contr_dl == dlevel) { 
#ifdef DEBUG
      std::cout << "The target level lit is " << from_expr(SSA.ns, "", *it) << std::endl;
#endif      
      target_level_lits.push_back(*it);
    }
    else
    {
      if(int(contr_dl) > max_reason_dl)
        max_reason_dl = int(contr_dl);
      
      new_result_clause.push_back(*it);
    }
#ifdef DEBUG  
    std::cout << "max_dl is" << max_reason_dl << "contr_dl " << contr_dl << "dlevel is " << dlevel << std::endl;
#endif     
 
  }
  new_result_clause.swap(result_clause);

  /* If the working set is empty, then we have chosen the wrong dlevel */
  if(target_level_lits.size() == 0)
  {
    assert(max_reason_dl >= 0);
    // go to that earlier dlevel, and try learning again from there
#ifdef DEBUG
    std::cout << "restarting search for UIP at level " << max_reason_dl << std::endl;
#endif
    find_uip(SSA, graph, result_clause, unsigned(max_reason_dl));
    return;
  }
  /* Set the backtracking level */
  assert(max_reason_dl != -1 || result_clause.size() == 0);
  if(max_reason_dl == -1)
  {
    //unit clause
    assert(result_clause.size() == 0);
    backtrack_level = 0;
  }
  else backtrack_level = max_reason_dl; 


#ifdef DEBUG
  std::cout << "The size of target_level_lits is " << target_level_lits.size() << std::endl;
#endif 
  /* If there is only one meet irreducible that conflicted
   * at present decision level, then use this as negated uip */
  if(target_level_lits.size() == 1) {
    result_clause.push_back(target_level_lits.front()); 
#ifdef DEBUG
    std::cout<< "UIP is" << target_level_lits.front() << std::endl;
#endif    
    return;
  }
  
  // There are more than one literals 
  // that contradict at dlevel, so start 
  // searching for uip now 

  assert(dlevel>0);
  // find the dlevel section of trail
  int trail_start = graph.control_trail[dlevel-1];
  int trail_end = 
    dlevel < graph.control_trail.size() ? 
    graph.control_trail[dlevel] - 1 : graph.prop_trail.size()-1;

  unsigned trail_size = (trail_end+1) - trail_start;

#ifdef DEBUG
  std::cout << "The DL section trail start is " << trail_start << "trail end is " << trail_end << std::endl;
#endif

  std::vector<bool> marked;
  marked.resize(trail_size, false);

  unsigned open_paths = target_level_lits.size();

  /* set initial marking for trail */
  for(int ws_i = 0; unsigned(ws_i) < target_level_lits.size(); ws_i++)
  {
    const exprt& lit = target_level_lits[ws_i];
    int index = first_contradiction_on_trail(lit, graph, trail_start, trail_end);
#ifdef DEBUG
    std::cout << "The first contradiction of the literal" << from_expr(SSA.ns, "", lit) << "is at " << index << std::endl;
#endif
    marked[index - trail_start] = true;
  }

  /* START OF UIP DETECTION */  
  int uip = -1;

  for(int i = trail_end; i >= trail_start; i--)
  {
    if(!marked[i-trail_start]) //skip unmarked ones
      continue;

    // ******** Marked portion of trail now ****** //
    //found uip
    if(open_paths == 1)
    {
      uip = i;
      break;
    }

    uip = i;
    // If a literal of the trail is in conflict, 
    // then this literal must have participated in 
    // any previous conflict clause to make it UNIT

    //int r = reason_trail[i]; assert(r != -1);
    //literalt l = lit_from_trail(i);  
    open_paths--;   
  }
  assert(uip != -1);
#ifdef DEBUG  
  std::cout << "UIP is " << graph.prop_trail[uip] << std::endl;
#endif
  negate(graph.prop_trail[uip], result_clause);
}
   
/*******************************************************************\

Function: acdl_analyze_conflict_baset::get_first_contradiction

 Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
int acdl_analyze_conflict_baset::first_contradiction_on_trail(
     const exprt& expr, acdl_conflict_grapht &graph, int trail_start, int trail_end)
{
  acdl_domaint::valuet relevant_expr;
  acdl_domaint::varst exp_symbols;
  find_symbols(expr, exp_symbols);

  for(int i = trail_start; i <= trail_end; i++)
  {
    exprt& trail_exp = graph.prop_trail[i];
    acdl_domaint::varst v_symbol;
    find_symbols(trail_exp, v_symbol);
    for(acdl_domaint::varst::iterator it1 = v_symbol.begin(); it1 != v_symbol.end(); it1++) {
      bool is_in = exp_symbols.find(*it1) != exp_symbols.end();
      if(is_in) {
        bool status = domain.compare(expr, trail_exp);
        if(status == domain.CONFLICT)
          return i;
      } 
    }   
  }
  assert(0);
}


/*******************************************************************\

Function: acdl_analyze_conflict_baset::get_latest_contradiction

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
  
unsigned acdl_analyze_conflict_baset::get_latest_contradiction(
const local_SSAt &SSA, acdl_conflict_grapht &graph, acdl_domaint::meet_irreduciblet &exp) 
{
  
  acdl_domaint::varst exp_symbols;
  // get symbols from this meet irreducible
  find_symbols(exp, exp_symbols);
  
#ifdef DEBUG  
  std::cout << "Searching for latest contradiction of literal" << from_expr(SSA.ns, "", exp) << std::endl;
#endif  

#ifdef DEBUG  
  std::cout << "searching for contradiction at the current level" << std::endl;
#endif  
  acdl_domaint::valuet matched_expr;
  int control_point = graph.control_trail.back(); 
  // traverse from the back of prop_trail, last element is false_exprt 
  // since the deduction at the current level leads to conflict, 
  // so the deduction are by construction UNSAT
  // so, we need to iterate over all elements explicitly
  // for this segment of propagation trail which corresponds to 
  // the current decision level. For other decision levels, we do 
  // not need to explicitly traverse the propagation trail segment 
  for(unsigned j=graph.prop_trail.size()-1;j>=control_point;j--)
  {
    //std::cout << "The matched expression is: " << from_expr(SSA.ns, "", graph.prop_trail[j]) << std::endl;
    assert(graph.prop_trail[graph.prop_trail.size()-1] == false_exprt());
    // find contradiction by traversing the prop_trail
    // and finding the relevant meet irreducibles  
    exprt prop_exp = graph.prop_trail[j];
    acdl_domaint::varst prop_symbols;
    // get symbols from this meet irreducible
    find_symbols(prop_exp, prop_symbols);
    // check if this symbol is in exp_symbols  
    for(acdl_domaint::varst::iterator it = prop_symbols.begin(); it != prop_symbols.end(); it++)
    {
      bool is_in = exp_symbols.find(*it) != exp_symbols.end();
      if(is_in) { 
        //std::cout << "Hey !!! found contradiction with " << from_expr(SSA.ns, "", prop_exp) << std::endl;
        matched_expr.push_back(prop_exp);
        break;
      }
    }
    #if 0
    exprt prop_exp = graph.prop_trail[j];
    if(prop_exp != false_exprt()) {
       std::cout << "The matched expression is: " << from_expr(SSA.ns, "", prop_exp) << std::endl;
      matched_expr.push_back(prop_exp);
    }
    #endif
  }
  // push the contradicted literal
  matched_expr.push_back(exp);
  bool status = domain.check_val_satisfaction(matched_expr);
  if(status == 0)
  {
#ifdef DEBUG  
    std::cout << "Found contradiction at current decision level for " << from_expr(SSA.ns, "", exp) << std::endl;
#endif    
    return graph.current_level;
  }
  // search for contradiction at decision level less than current level
  else {
#ifdef DEBUG  
   std::cout << "No contradiction found at current decision level" << std::endl; 
#endif   
   unsigned lower_index, upper_index;
   unsigned control_trail_size = graph.control_trail.size();
   int search_level = control_trail_size-1;
   while(search_level >= 0) {
     acdl_domaint::valuet val_perdecision;

#ifdef DEBUG  
     std::cout << "searching for contradiction at level: " << search_level << std::endl;
#endif
     upper_index = graph.control_trail[search_level];
     if(search_level-1 >= 0)
       lower_index = graph.control_trail[search_level-1];
     else 
       lower_index = 0; 
#ifdef DEBUG  
     std::cout << "Upper index is " << upper_index << "lower index is " << lower_index << std::endl;
#endif     
     // now traverse the prop_trail  
     for(unsigned k=upper_index-1;k>=lower_index;k--) {
       //std::cout << "The matched expression is: " << from_expr(SSA.ns, "", graph.prop_trail[k]) << std::endl;
       assert(k >= 0);
       exprt prop_exp = graph.prop_trail[k];
       val_perdecision.push_back(prop_exp);
       if(k==0) break;
     }
     // assert that the deductions for this decision are consistent 
     assert(domain.check_val_consistency(val_perdecision));
     // push the contradicted literal
     val_perdecision.push_back(exp);
     bool status = domain.check_val_satisfaction(val_perdecision);
     if(status == 0)
     {
#ifdef DEBUG  
       std::cout << "Found contradiction at decision level:" << search_level << "for " << from_expr(SSA.ns, "", exp) << std::endl;
#endif       
       return search_level;
     }
     search_level=search_level-1;
   }
  }
}



/*******************************************************************\

Function: acdl_analyze_conflict_baset::get_earliest_contradiction

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
  
unsigned acdl_analyze_conflict_baset::get_earliest_contradiction(
const local_SSAt &SSA, acdl_conflict_grapht &graph, acdl_domaint::meet_irreduciblet &exp) 
{
  acdl_domaint::varst exp_symbols;
  // get symbols from this meet irreducible
  find_symbols(exp, exp_symbols);
  
#ifdef DEBUG  
  std::cout << "Searching for earliest contradiction of literal " << from_expr(SSA.ns, "", exp) << std::endl;
#endif  
  // search for contradiction from beginning
 
   unsigned lower_index, upper_index;
   unsigned control_trail_size = graph.control_trail.size();
   int search_level = 0;
   while(search_level <= control_trail_size-1) {
     acdl_domaint::valuet val_perdecision;

#ifdef DEBUG  
     std::cout << "searching for contradiction at level " << search_level << std::endl;
#endif     
     upper_index = graph.control_trail[search_level];
     if(search_level == 0)
       lower_index = 0; 
     else 
       lower_index = graph.control_trail[search_level-1];
#ifdef DEBUG  
     std::cout << "Upper index is " << upper_index << "lower index is " << lower_index << std::endl;
#endif     
     // [TODO] check for empty propagation trail
     if(upper_index == lower_index) { 
       search_level=search_level+1;
       continue;
     }
     // now traverse the prop_trail  
     for(unsigned k=lower_index;k<=upper_index-1;k++) {
       //std::cout << "The matched expression is: " << from_expr(SSA.ns, "", graph.prop_trail[k]) << std::endl;
       assert(k >= 0);
       exprt prop_exp = graph.prop_trail[k];
       val_perdecision.push_back(prop_exp);
       if(k==upper_index-1) break;
     }
     // assert that the deductions for this decision are consistent 
     assert(domain.check_val_consistency(val_perdecision));
     // push the contradicted literal
     val_perdecision.push_back(exp);
     bool status = domain.check_val_satisfaction(val_perdecision);
     if(status == 0)
     {
#ifdef DEBUG  
       std::cout << "Found contradiction at decision level " << search_level << "for " << from_expr(SSA.ns, "", exp) << std::endl;
#endif       
       return search_level;
     }
     search_level=search_level+1;
   }
  
#ifdef DEBUG  
  std::cout << "searching for contradiction at the current level" << std::endl;
#endif  
  acdl_domaint::valuet matched_expr;
  int control_point = graph.control_trail.back(); 
  // traverse from the back of prop_trail, last element is false_exprt 
  // since the deduction at the current level leads to conflict, 
  // so the deduction are by construction UNSAT
  // so, we need to iterate over all elements explicitly
  // for this segment of propagation trail which corresponds to 
  // the current decision level. For other decision levels, we do 
  // not need to explicitly traverse the propagation trail segment 
  for(unsigned j=control_point;j<=graph.prop_trail.size()-1;j++)
  {
    //std::cout << "The matched expression is: " << from_expr(SSA.ns, "", graph.prop_trail[j]) << std::endl;
    assert(graph.prop_trail[graph.prop_trail.size()-1] == false_exprt());
    // find contradiction by traversing the prop_trail
    // and finding the relevant meet irreducibles  
    exprt prop_exp = graph.prop_trail[j];
    acdl_domaint::varst prop_symbols;
    // get symbols from this meet irreducible
    find_symbols(prop_exp, prop_symbols);
    // check if this symbol is in dec_symbols  
    for(acdl_domaint::varst::iterator it = prop_symbols.begin(); it != prop_symbols.end(); it++)
    {
      bool is_in = exp_symbols.find(*it) != exp_symbols.end();
      if(is_in) { 
        //std::cout << "Hey !!! found contradiction with " << from_expr(SSA.ns, "", prop_exp) << std::endl;
        matched_expr.push_back(prop_exp);
        break;
      }
    }
    #if 0
    exprt prop_exp = graph.prop_trail[j];
    if(prop_exp != false_exprt()) {
       std::cout << "The matched expression is: " << from_expr(SSA.ns, "", prop_exp) << std::endl;
      matched_expr.push_back(prop_exp);
    }
    #endif
  }
  // push the contradicted literal
  matched_expr.push_back(exp);
  bool status = domain.check_val_satisfaction(matched_expr);
  if(status == 0)
  {
#ifdef DEBUG  
    std::cout << "Found contradiction at current decision level for " << from_expr(SSA.ns, "", exp) << std::endl;
#endif    
    return graph.current_level;
  }
}
