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
  
  // check that the clause is unit
  //assert(unit_rule(conflict_clause));
  
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
     find_uip(SSA, graph, conf_clause, backtrack_level);
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
  while(graph.prop_trail.size() > graph.control_trail.size()) 
  {
    graph.val_trail.pop_back();
    graph.prop_trail.pop_back();
  } 
  
  graph.control_trail.pop_back();
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
  std::vector<exprt> dec_symbols;
  exprt exp;
  for(unsigned i=0;i<graph.dec_trail.size();i++)
  {
    exprt dec_exp = graph.dec_trail[i];
    if(dec_exp.id() == ID_not)
      exp = dec_exp.op0();
    else
      exp = dec_exp;  
    
    // expressions of the form guard#0
    if(exp.id() != ID_le && exp.id() != ID_ge) 
    {
      dec_symbols.push_back(exp); 
    }
    else if(exp.id() == ID_lt || exp.id() == ID_gt 
          || exp.id() == ID_le || exp.id() == ID_ge) 
    {
       exprt lhs = to_binary_relation_expr(exp).lhs();
       //std::vector<exprt>iterator it; 
       //it = find(dec_symbols.begin(), dec_symbols.end(), lhs)
       dec_symbols.push_back(lhs);  
    }
  }
  #endif

  for(unsigned i=0;i<graph.dec_trail.size();i++)
  {
    exprt dec_exp = graph.dec_trail[i];
    reason.push_back(dec_exp);
  }
  // now normalize the reason since there may be 
  // lot of redundant decisions 
  domain.normalize(reason);

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
acdl_conflict_grapht &graph, acdl_domaint::valuet &result_clause, int blevel)
{
  assert(result_clause.size() != 0);
#ifdef DEBUG
  std::cout << "searching for uip" << std::endl;
#endif 

  if(graph.current_level == 0)
  { 
    std::cout << "Trying to resolve a conflict a dlevel 0" << std::endl;
    blevel = -1; //UNSAT
    return;
  }

  acdl_domaint::valuet target_level_lits;
  int max_reason_dl = -1;
  acdl_domaint::valuet new_result_clause;
  for(acdl_domaint::valuet::iterator it = result_clause.begin(); 
      it != result_clause.end(); ++it)
  {
    unsigned contr_dl = get_earliest_contradiction(SSA, graph, *it);

    assert(contr_dl <= graph.current_level);

    if(contr_dl == graph.current_level)
      target_level_lits.push_back(*it);
    else
    {
      if(int(contr_dl) > max_reason_dl)
        max_reason_dl = int(contr_dl);

      new_result_clause.push_back(*it);
    }
  }
  new_result_clause.swap(result_clause);
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
  //control_trail_size = graph.control_trail.size();
  //while(control_trail_size != 0) {
  
  acdl_domaint::varst exp_symbols;
  // get symbols from this meet irreducible
  find_symbols(exp, exp_symbols);
  
  std::cout << "searching for contradiction at the current level" << std::endl;
  acdl_domaint::valuet matched_expr;
  int control_point = graph.control_trail.back(); 
  // traverse from the back of prop_trail 
  for(unsigned j=graph.prop_trail.size()-1;j>control_point;j--)
  {
    exprt prop_exp = graph.prop_trail[j];
    acdl_domaint::varst prop_symbols;
    // get symbols from this meet irreducible
    find_symbols(prop_exp, prop_symbols);
    // check if this symbol is in dec_symbols  
    for(acdl_domaint::varst::iterator it = prop_symbols.begin(); it != prop_symbols.end(); it++)
    {
      bool is_in = exp_symbols.find(*it) != exp_symbols.end();
      if(is_in) { 
        matched_expr.push_back(prop_exp);
        break;
      }
    }   
  }
  bool status = domain.check_val_consistency(matched_expr);
  if(status == 1)
  {
    std::cout << "Found contradiction at current decision level" << std::endl;
    return graph.current_level;
  }
  // search for contradiction at decision level less than current level
  else {
   std::cout << "searching for contradiction at level: " << std::endl;




  }
}

