/*******************************************************************\

Module: ACDL Clause Learning Base

Author: Rajdeep Mukherjee, Peter Schrammel

\*******************************************************************/

#include <util/find_symbols.h>
#include "acdl_analyze_conflict_base.h"

#define DEBUG

/*******************************************************************\

Function: abstr_dpll_searcht::chronological_backtrack
 
  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
bool acdl_analyze_conflict_baset::chronological_backtrack(const local_SSAt &SSA, acdl_conflict_grapht &graph)
{
  std::cout << "inside backtrack" << std::endl;
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
   
  // backtrack one level
  cancel_once(SSA, graph);
  
  // flip the expression
  exprt exp = flip(dec_exp);

  graph.assign_to_trail(exp);
  
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
  
  // add the conflict clause to the learned clause database
  learned_clauses.push_back(conf_clause);
  
  // backtrack
  std::cout << "****************" << std::endl;
  std::cout << "BACKTRACK PHASE" << std::endl;
  std::cout << "****************" << std::endl;
#ifdef DEBUG
  std::cout << "backtrack to dlevel: " << backtrack_level << std::endl;
#endif  
  cancel_until(SSA,graph,backtrack_level);
  
  backtracks++;
  
  exprt unit_lit;
  acdl_domaint::valuet v;
  graph.to_value(v);
  // check that the clause is unit
  int result = domain.unit_rule(SSA, v, conf_clause, unit_lit);
  
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
     std::cout << "Conflict is purely Propositional" << std::endl;
   }
   // conflict is caused by Abstract Interpretation proof
   else if(last_proof == ABSINT) {
     acdl_domaint::valuet reason;
     get_ai_reason(SSA, graph, reason);

     for(acdl_domaint::valuet::iterator it = reason.begin();
          it != reason.end(); it++)
     {
       negate(*it, conf_clause);
     } 
     std::cout << "Conflict is purely from Abstract Interpretation Proof" << std::endl;
   }

   if(conf_clause.size() == 0)
     backtrack_level = -1;
   else 
     find_uip(SSA, graph, conf_clause, graph.current_level);
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
    std::cout << "Trying to resolve a conflict at dlevel 0" << std::endl;
    backtrack_level = -1; //UNSAT
    return;
  }

  acdl_domaint::valuet target_level_lits;
  int max_reason_dl = -1;
  acdl_domaint::valuet new_result_clause;
  for(acdl_domaint::valuet::iterator it = result_clause.begin(); 
      it != result_clause.end(); ++it)
  {
    unsigned contr_dl = get_earliest_contradiction(SSA, graph, *it);
    std::cout << "The contradicted decision level is " << contr_dl << std::endl;
    assert(contr_dl <= dlevel);

    if(contr_dl == dlevel)
      target_level_lits.push_back(*it);
    else
    {
      if(int(contr_dl) > max_reason_dl)
        max_reason_dl = int(contr_dl);

      new_result_clause.push_back(*it);
    }
  }
  new_result_clause.swap(result_clause);

  /* If the working set is empty, then we have chosen the wrong dlevel */
  if(target_level_lits.size() == 0)
  {
    assert(max_reason_dl >= 0);
    // go to that earlier dlevel, and try learning again from there
#ifdef VERBOSE
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
 
  /* If there is only one meet irreducible that conflicted
   * at present decision level, then use this as negated uip */
  if(target_level_lits.size() == 1)
    result_clause.push_back(target_level_lits.front()); 
#ifdef DEBUG
    std::cout<< "UIP is" << target_level_lits.front() << std::endl;
#endif    
   return;

   // start actually searching for uip
   
   assert(dlevel>0);
   // find the dlevel section of trail
   
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
  
  std::cout << "Searching for earliest contradiction of literal" << from_expr(SSA.ns, "", exp) << std::endl;

  std::cout << "searching for contradiction at the current level" << std::endl;
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
    std::cout << "The matched expression is: " << from_expr(SSA.ns, "", graph.prop_trail[j]) << std::endl;
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
        std::cout << "Hey !!! found contradiction with " << from_expr(SSA.ns, "", prop_exp) << std::endl;
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
    std::cout << "Found contradiction at current decision level for " << from_expr(SSA.ns, "", exp) << std::endl;
    return graph.current_level;
  }
  // search for contradiction at decision level less than current level
  else {
   std::cout << "No contradiction found at current decision level" << std::endl; 
   unsigned lower_index, upper_index;
   unsigned control_trail_size = graph.control_trail.size();
   int search_level = control_trail_size-1;
   while(search_level >= 0) {
     acdl_domaint::valuet val_perdecision;

     std::cout << "searching for contradiction at level: " << search_level << std::endl;
     upper_index = graph.control_trail[search_level];
     if(search_level-1 >= 0)
       lower_index = graph.control_trail[search_level-1];
     else 
       lower_index = 0; 
     std::cout << "Upper index is " << upper_index << "lower index is " << lower_index << std::endl;
     // now traverse the prop_trail  
     for(unsigned k=upper_index-1;k>=lower_index;k--) {
       std::cout << "The matched expression is: " << from_expr(SSA.ns, "", graph.prop_trail[k]) << std::endl;
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
       std::cout << "Found contradiction at decision level:" << search_level << "for " << from_expr(SSA.ns, "", exp) << std::endl;
       return search_level;
     }
     search_level=search_level-1;
   }
  }
}
