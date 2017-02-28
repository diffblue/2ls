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
#ifdef DEBUG
  std::cout << "inside backtrack" << std::endl;
#endif
  if(graph.current_level==0) {
    backtrack_level=-1; // no further backtrack possible
    return false;
  }

  unsigned first_idx=graph.control_trail.back();

#ifdef DEBUG
  std::cout << "val_trail size is: " << graph.val_trail.size() << "control_trail.back is: "  << first_idx << std::endl;
#endif
  assert(graph.val_trail.size() >= first_idx+1);
  exprt dec_exp=graph.prop_trail[first_idx];

  // check val_trail and prop_trail are of equal size
  assert(graph.prop_trail.size()==graph.val_trail.size());

#ifdef DEBUG
  std::cout << "The decision to be flipped is " << from_expr(SSA.ns, "", dec_exp);
  std::cout << "The trail before  backtracking is" << std::endl;
#endif
  graph.dump_trail(SSA);

  // backtrack one level
  cancel_once(SSA, graph);

  // flip the expression
  exprt exp=flip(dec_exp);

  graph.assign_to_trail(exp);

#ifdef DEBUG
  std::cout << "The trail after backtracking and assigning negation of previous decision is" << std::endl;
#endif
  graph.dump_trail(SSA);

  // check val_trail and prop_trail are of
  // equal size after backtracking
  assert(graph.prop_trail.size()==graph.val_trail.size());

  // update the backtrack level
  backtrack_level=graph.current_level;

  just_backtracked=true;

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
  if(backtrack_level<0) {
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
  //int present_dl=graph.current_level;
  // save the last decision before backtracking
  exprt dec_expr=graph.dec_trail.back();

  // backtrack
  std::cout << "****************" << std::endl;
  std::cout << "BACKTRACK PHASE" << std::endl;
  std::cout << "****************" << std::endl;
#ifdef DEBUG
  std::cout << "backtrack to dlevel: " << backtrack_level << std::endl;
#endif
  cancel_until(SSA, graph, backtrack_level);
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

  // preprocess abstract value: 
  // transform constraints like 
  // (x==n) to (x<=n) and (x>=n)
  preprocess_val(v);
#ifdef debug
  std::cout << "preprocessed abstract value of implication graph: " << std::endl;
  for(acdl_domaint::valuet::const_iterator it=v.begin();it!=v.end(); ++it)
    std::cout << from_expr(ssa.ns, "", *it) << std::endl;
#endif


  // check that the clause is unit,
  // this causes one propagation because
  // the clause is unit
  acdl_domaint::clause_state result=domain.unit_rule(SSA, v, norm_conf_clause, unit_lit);

  // the learned clause must be asserting
  assert(result==3); //(result==UNIT)

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
  assert(graph.prop_trail.size()-graph.control_trail.size() >= 2);

  just_backtracked=true;
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
  if(last_proof==PROPOSITIONAL) {
    assert(conflicting_clause!=-1);
    conf_clause=learned_clauses[conflicting_clause];
#ifdef DEBUG
    std::cout << "Conflict is purely Propositional" << std::endl;
#endif
  }
  // conflict is caused by Abstract Interpretation proof
  else if(last_proof==ABSINT) {
    acdl_domaint::valuet reason;
    get_ai_reason(SSA, graph, reason);
    // print the reason
#ifdef DEBUG
    std::cout << "Reason: " << from_expr(SSA.ns, "", disjunction(reason)) << std::endl;
#endif

    for(acdl_domaint::valuet::iterator it=reason.begin();
        it!=reason.end(); it++)
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
  if(conf_clause.size()==0)
    backtrack_level=-1;
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
    // if(graph.current_level==0) return;
    cancel_once(SSA, graph);
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

 Purpose: Make sure that the value returned from here contains 
 elements from different decision levels. And there are more than 
 one elements in the current decision level. If there are only one
 element in the current decision level, then finding UIP becomes
 trivial.

\*******************************************************************/

void acdl_analyze_conflict_baset::get_ai_reason(const local_SSAt &SSA,
                                                acdl_conflict_grapht &graph, acdl_domaint::valuet &reason)
{
#if 0
  // collect all propagations in the reason
  // upto the point where first decision was made
  // iterate upto trail_size-2 since the last node
  // is a FALSE node
  int control_point=graph.control_trail[0];
  for(unsigned i=control_point;i<graph.prop_trail.size()-2;i++)
  {
    exprt prop_exp=graph.prop_trail[i];
    reason.push_back(prop_exp);
  }
#endif
#if 0
  // **********************************
  // Strategy 1: Collect all decisions
  // **********************************

  // just take all decisions as reason
  for(unsigned i=0;i<graph.dec_trail.size();i++)
  {
    exprt dec_exp=graph.dec_trail[i];
    reason.push_back(dec_exp);
  }
  // now normalize the reason since there may be
  // lot of redundant decisions
  // domain.normalize(reason);
#endif

  // *******************************************************************
  // Strategy 2: Collect all decisions 
  // upto "dl-1" and for "dl" level, do the following:
  // Step 1: Collect the meet irreducible
  // in trail that directly contradict with the final transformer
  // Step 2: If the above set in empty, then collect all meet irreducibles
  // that has same symbols as the last transformer that lead to conflict
  //
  // In both the cases, assert that the conjunction of the collected 
  // elements contradict with the final transformer.
  // *********************************************************************
  
  // collect all decisions up to dl-1 into reason array
  for(unsigned t=0;t<graph.dec_trail.size()-1;t++)
  {
    exprt dec_exp=graph.dec_trail[t];
    reason.push_back(dec_exp);
  }
  unsigned dlevel=graph.current_level;
  assert(dlevel>0);
  // find the dlevel section of trail
  int trail_start=graph.control_trail[dlevel-1];
  int trail_end=
    dlevel<graph.control_trail.size() ?
           graph.control_trail[dlevel]-1 : graph.prop_trail.size()-1;

#ifdef DEBUG
  std::cout << "The DL section trail start is " << trail_start << "trail end is " << trail_end << std::endl;

  for(int d=trail_end;d>=trail_start;d--)
    std::cout << "Trail element is " << from_expr(graph.prop_trail[d]) << std::endl;
#endif

  // collect the last transformer 
  // that leads to conflict
  const acdl_domaint::statementt stmt = graph.reason_trail[trail_end].first;

  acdl_domaint::varst stmt_symbols;
  // get symbols from this meet irreducible
  find_symbols(stmt, stmt_symbols);

#ifdef DEBUG
  std::cout << "The current transformer is " << from_expr(stmt) << std::endl;
#endif

  for(int i=trail_end; i>=trail_start; i--)
  {
    exprt trail_exp=graph.prop_trail[i];
#ifdef DEBUG
        std::cout << "The meet irreducible checked for contradiction at current decision level is " 
          << from_expr(trail_exp) << std::endl;
#endif
    if(trail_exp == false_exprt()) continue;
    else {

      // Step 1: Collect the meet irreducible
      // in trail that directly contradict with the final transformer
#ifdef DEBUG
        std::cout << "Checking whether the meet irreducible " 
          << from_expr(trail_exp) << "contradict with the transformer " 
          << from_expr(stmt) << std::endl;
#endif
      std::unique_ptr<incremental_solvert> solver(
          incremental_solvert::allocate(SSA.ns, true));
      *solver << and_exprt(trail_exp, stmt);
      decision_proceduret::resultt result=(*solver)();
      if(result==decision_proceduret::D_UNSATISFIABLE) {
#ifdef DEBUG
        std::cout << "The meet irreducible " << from_expr(trail_exp) 
          << "directly contradict with the transformer " 
          << from_expr(stmt) << std::endl;
#endif
        reason.push_back(trail_exp);
        // only collect the first contradiction
        // and break from the for loop
        break;
      }
      // Step 2: If the above set in empty, then collect 
      // all meet irreducibles that has same symbols as the 
      // last transformer that lead to conflict
#ifdef DEBUG
        std::cout << "The meet irreducible " 
          << from_expr(trail_exp) << "did not contradict with the transformer " 
          << from_expr(stmt) << std::endl;
        std::cout << "Checking for matching symbols" << std::endl;
#endif
      acdl_domaint::varst prop_symbols;
      // get symbols from this meet irreducible
      find_symbols(trail_exp, prop_symbols);
      // check if this symbol is in dec_symbols
      for(acdl_domaint::varst::iterator it=prop_symbols.begin(); it!=prop_symbols.end(); it++)
      {
        bool is_in=stmt_symbols.find(*it)!=stmt_symbols.end();
        if(is_in) {
#ifdef DEBUG
          std::cout << "Found matching symbols, put " 
            << from_expr(SSA.ns, "", trail_exp) 
            << " into reason array" << std::endl;
#endif
          reason.push_back(trail_exp);
        }
      }
    }
  }
#ifdef DEBUG
  std::cout << "The initial reason is " << std::endl;
  for(unsigned j=0;j<reason.size();j++)
    std::cout << "Reason element:: " << from_expr(reason[j]) << std::endl;
#endif
#if 0
  // assert that the entries in reason trail 
  // leads to conflict when conjoined with the transformers
  acdl_domaint::valuet stmt_val;
  for(unsigned k=0;k<graph.reason_trail.size();k++)
    stmt_val.push_back(graph.reason_trail[k].first);
#endif

#ifdef DEBUG
  std::cout << "Checking that the initial reason leads to conflict " << std::endl;
#endif

  std::unique_ptr<incremental_solvert> solver(
      incremental_solvert::allocate(SSA.ns, true));
  *solver << and_exprt(stmt, conjunction(reason));
  decision_proceduret::resultt result=(*solver)();
  assert(result==decision_proceduret::D_UNSATISFIABLE);
#ifdef DEBUG
  std::cout << "The initial reason " 
    << from_expr(conjunction(reason)) << " leads to conflict with the transformer " 
    << from_expr(stmt) << std::endl;
#endif

#if 0
  // Step 1: collect all decision variables by traversing the decision trail
  // (decisions follow the templates x<=0, y>10)
  // Step 2: traverse the prop_trail from back and collect the meet
  // irreducibles involving these variables
  // Step 3: Store these meet irreducibles from step 2 in reason

  acdl_domaint::varst dec_symbols;
  for(unsigned i=0;i<graph.dec_trail.size();i++)
  {
    exprt dec_exp=graph.dec_trail[i];
    acdl_domaint::varst symbols;
    find_symbols(dec_exp, symbols);
    dec_symbols.insert(symbols.begin(), symbols.end());
  }
#ifdef DEBUG
  std::cout << "Print all decision symbols so far: " << std::endl;
  for(acdl_domaint::varst::iterator it=dec_symbols.begin(); it!=dec_symbols.end(); it++)
    std::cout << *it << std::endl;
#endif

  int control_point=graph.control_trail.back();
  // traverse from the back of prop_trail to
  // get the latest value, retrieve latest values
  // from only this deduction stage
  for(unsigned j=graph.prop_trail.size()-1;j>control_point;j--)
  {
    exprt prop_exp=graph.prop_trail[j];
    acdl_domaint::varst prop_symbols;
    // get symbols from this meet irreducible
    find_symbols(prop_exp, prop_symbols);
    // check if this symbol is in dec_symbols
    for(acdl_domaint::varst::iterator it=prop_symbols.begin(); it!=prop_symbols.end(); it++)
    {
      bool is_in=dec_symbols.find(*it)!=dec_symbols.end();
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
  assert(result_clause.size()!=0);
#ifdef DEBUG
  std::cout << "searching for uip" << std::endl;
#endif

  if(dlevel==0)
  {
#ifdef DEBUG
    std::cout << "Trying to resolve a conflict at dlevel 0" << std::endl;
#endif
    backtrack_level=-1; // UNSAT
    return;
  }

  acdl_domaint::valuet target_level_lits;
  int max_reason_dl=-1;
  acdl_domaint::valuet new_result_clause;

  //int clause_size=result_clause.size();

  unsigned contr_dl=0;
  for(acdl_domaint::valuet::iterator it=result_clause.begin();
      it!=result_clause.end(); ++it)
  {
    contr_dl=get_earliest_contradiction(SSA, graph, *it);
#ifdef DEBUG
    std::cout << "The contradicted decision level is " << contr_dl << std::endl;
#endif
    assert(contr_dl<=dlevel);
#ifdef DEBUG
    std::cout << "Comparing max_dl " << max_reason_dl << "contr_dl " << contr_dl << std::endl;
#endif
    if(contr_dl==dlevel) {
#ifdef DEBUG
      std::cout << "The target level lit is " << from_expr(SSA.ns, "", *it) << std::endl;
#endif
      target_level_lits.push_back(*it);
    }
    else
    {
      if(int(contr_dl) > max_reason_dl)
        max_reason_dl=int(contr_dl);

      new_result_clause.push_back(*it);
    }
#ifdef DEBUG
    std::cout << "max_dl is" << max_reason_dl << "contr_dl " << contr_dl << "dlevel is " << dlevel << std::endl;
#endif

  }
  new_result_clause.swap(result_clause);

  /* If the working set is empty, then we have chosen the wrong dlevel */
  if(target_level_lits.size()==0)
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
  assert(max_reason_dl!=-1 || result_clause.size()==0);
  if(max_reason_dl==-1)
  {
    // unit clause
    assert(result_clause.size()==0);
    backtrack_level=0;
  }
  else backtrack_level=max_reason_dl;


#ifdef DEBUG
  std::cout << "The size of target_level_lits is " << target_level_lits.size() << std::endl;
#endif
  /* If there is only one meet irreducible that conflicted
   * at present decision level, then use this as negated uip */
  if(target_level_lits.size()==1) {
    result_clause.push_back(target_level_lits.front());
#ifdef DEBUG
    std::cout<< "UIP is" << from_expr(target_level_lits.front()) << std::endl;
#endif
    return;
  }

  // There are more than one literals
  // that contradict at dlevel, so start
  // searching for uip now

  assert(dlevel>0);
  // find the dlevel section of trail
  int trail_start=graph.control_trail[dlevel-1];
  int trail_end=
    dlevel<graph.control_trail.size() ?
           graph.control_trail[dlevel]-1 : graph.prop_trail.size()-1;

  unsigned trail_size=(trail_end+1)-trail_start;

#ifdef DEBUG
  std::cout << "The DL section trail start is " << trail_start << "trail end is " << trail_end << std::endl;
  dump_section(trail_start, trail_end, graph);
#endif

  std::vector<bool> marked;
  marked.resize(trail_size, false);

  unsigned open_paths=target_level_lits.size();

  /* set initial marking for trail */
  for(int ws_i=0; unsigned(ws_i)<target_level_lits.size(); ws_i++)
  {
    const exprt& lit=target_level_lits[ws_i];
    int index=first_contradiction_on_trail(lit, graph, trail_start, trail_end);
#ifdef DEBUG
    std::cout << "The first contradiction of the literal" << from_expr(SSA.ns, "", lit) << "is at " << index << std::endl;
#endif
    marked[index-trail_start]=true;
  }

  /* START OF UIP DETECTION */
  int uip=-1;

  for(int i=trail_end; i >= trail_start; i--)
  {
    if(!marked[i-trail_start]) // skip unmarked ones
      continue;

    // ******** Marked portion of trail now ****** //
    // found uip
    if(open_paths==1)
    {
      uip=i;
      break;
    }

    // find corresponding reason from reason trail
    const acdl_domaint::statementt stmt = graph.reason_trail[i].first;
    
    // [CHECK ??] antecedent clause must be non-unit
    // assert(stmt.size()>1);
    
    // bool asserting_lit = false;


#ifdef DEBUG
    std::cout << "Stepping through antecedent clause " << std::endl;
#endif
    // construct init_value from elements in 
    // the beginning of trail to (i-1)th element
    acdl_conflict_grapht::indext ind=graph.reason_trail[i].second;
    unsigned end_index=ind.first;
    // find initial_value
    acdl_domaint::valuet init_value;
    for(unsigned k=0;k<=end_index-1;k++)
      init_value.push_back(graph.prop_trail[k]);

    // compute the final value
    unsigned a=ind.first;
    unsigned b=ind.second;
    acdl_domaint::valuet final_value;
    // [TODO] check the index a and b 
#ifdef DEBUG
    std::cout << "The deductions corresponding to the transformer " << from_expr(stmt) << "are " << std::endl;
#endif
    for(unsigned t=a;t<=b;t++) {
#ifdef DEBUG
      std::cout << "The deductions corresponding to the transformer " << from_expr(stmt) << "are " << std::endl;
#endif
      std::cout << "Deduction:: " << from_expr(graph.prop_trail[t]) << std::endl;
      final_value.push_back(graph.prop_trail[t]);
    }
    
    // collect all symbols from 
    // transformer and initial value
    acdl_domaint::varst tvars;
    find_symbols(stmt, tvars);
    for(acdl_domaint::valuet::iterator iti=init_value.begin();
        iti!=init_value.end(); iti++) 
    {
      acdl_domaint::varst symbols;
      find_symbols(*iti, symbols);
      tvars.insert(symbols.begin(), symbols.end());
    }
    acdl_domaint::valuet generalized_value;
    unsigned dec_level=0;
    // call the abductive generalization transformer
#ifdef DEBUG
    std::cout << "Applying abductive underapproximate transformer " << std::endl;
    std::cout << "Input: Initial value:: " 
      << from_expr(conjunction(init_value)) << std::endl;
    std::cout << "Input: Antecedent clause:: " 
      << from_expr(stmt) << std::endl;
    std::cout << "Input: Final value:: " 
      << from_expr(conjunction(final_value)) << std::endl;
    std::cout << "Input: Variable set:: ";
    for(acdl_domaint::varst::iterator
        it1=tvars.begin();it1!=tvars.end(); it1++)
      std::cout << from_expr(SSA.ns, "", *it1) << " ";
    std::cout << std::endl;
#endif

#ifdef DEBUG
    std::cout << "Perfoming Abduction" << std::endl;
    acdl_domaint::valuet reason;
    get_reason(SSA, stmt, init_value, final_value, reason);
#endif

#ifdef DEBUG
    std::cout << "Perfoming Generalization" << std::endl;
#endif
    domain(stmt,tvars,init_value,final_value,generalized_value);
    
#ifdef DEBUG
    std::cout << "Output: Generalization of Initial value:: " 
      << from_expr(conjunction(generalized_value)) << std::endl;
#endif
    
    // iterate over generalized_value and 
    // find comparable elements of the 
    // generalized value in the trail 
    for(acdl_domaint::valuet::iterator it=generalized_value.begin();
        it!=generalized_value.end(); it++) 
    {
      dec_level = find_generalization_on_trail(SSA, graph, *it);

      if(dec_level==0) {
        std::cout << "No generalizations found !! " << std::endl;
        // [TODO] Check for decision level 0
        assert(0);
      }
      if(dec_level < dlevel)
      {
        // generalization on earlier decision level
        // add to the result clause
        result_clause.push_back(*it);
        int l=dec_level;
        if(l > backtrack_level)
          backtrack_level = l;
      }
      else
      {
        // contradiction at current decision level
        // so, mark the trail
#ifdef DEBUG
        std::cout << "Found matching generalized comparable element at current decision level " << std::endl;
#endif
        int ind_gen = first_generalization_on_trail(*it, graph, trail_start, trail_end);
        // assert that there are comparable elements 
        // in the trail 
        assert(ind_gen!=-1);
#ifdef DEBUG
        std::cout << "The first generalization of" << from_expr(SSA.ns, "", *it) << "is at " << ind_gen << std::endl;
#endif
        // update the prop_trail with the generalized element
        graph.prop_trail[ind_gen]=*it;

        // update the marked data structure
        if(!marked[ind_gen-trail_start]) 
          open_paths++;
        
        marked[ind_gen-trail_start]=true;
      }
    } 
    open_paths--;
  }
  assert(uip!=-1);
#ifdef DEBUG
  std::cout << "UIP is " << from_expr(graph.prop_trail[uip]) << std::endl;
#endif
  negate(graph.prop_trail[uip], result_clause);
}

/*******************************************************************\

Function: acdl_analyze_conflict_baset::find_generalization_on_trail

 Inputs:

 Outputs:

 Purpose: returns a decision level where it finds a generalization 
 of an element in the trail

\*******************************************************************/
unsigned acdl_analyze_conflict_baset::find_generalization_on_trail(const local_SSAt &SSA, acdl_conflict_grapht &graph, exprt &exp)
{

#ifdef DEBUG
  std::cout << "Searching for earliest generalization of literal " << from_expr(SSA.ns, "", exp) << std::endl;
#endif
  // search for contradiction from beginning

  unsigned lower_index, upper_index;
  unsigned control_trail_size=graph.control_trail.size();
  unsigned search_level=0;
  while(search_level<=control_trail_size-1) {
    acdl_domaint::valuet val_perdecision;

#ifdef DEBUG
    std::cout << "searching for contradiction at level " << search_level << std::endl;
#endif
    upper_index=graph.control_trail[search_level];
    if(search_level==0)
      lower_index=0;
    else
      lower_index=graph.control_trail[search_level-1];
#ifdef DEBUG
    std::cout << "Upper index is " << upper_index << "lower index is " << lower_index << std::endl;
#endif
    // [TODO] check for empty propagation trail
    if(upper_index==lower_index) {
      search_level=search_level+1;
      continue;
    }
    // now traverse the prop_trail
    unsigned index_level=first_generalization_on_trail(exp,graph,lower_index,upper_index-1);
    if(index_level>=0) {
#ifdef DEBUG
    std::cout << "Found generalization at decision level " << search_level << "for " << from_expr(SSA.ns, "", exp) << std::endl;
#endif
      return search_level;
    }

    search_level=search_level+1;
  }

#ifdef DEBUG
  std::cout << "searching for contradiction at the current level" << std::endl;
#endif
  acdl_domaint::valuet matched_expr;
  int control_point=graph.control_trail.back();
  assert(graph.prop_trail[graph.prop_trail.size()-1]==false_exprt());
  unsigned gen_level=first_generalization_on_trail(exp,graph,control_point,graph.prop_trail.size()-1);
  if(gen_level>=0) {
#ifdef DEBUG
    std::cout << "Found generalization at current decision level for " << from_expr(SSA.ns, "", exp) << std::endl;
#endif
    return graph.current_level;
  }
  
  // if the control reaches here, 
  // that means no contradiction 
  // has been found at previous levels
  return 0;
}

/*******************************************************************\

Function: acdl_analyze_conflict_baset::first_generalization_on_trail

 Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
unsigned acdl_analyze_conflict_baset::first_generalization_on_trail(
  exprt &expr, acdl_conflict_grapht &graph, int trail_start, int trail_end)
{
  exprt expr_norm, trail_exp_norm;
  domain.normalize_meetirrd(expr, expr_norm);
  mp_integer val1, val2;
  if(expr_norm.id()!=ID_le && expr_norm.id()!=ID_ge)
  { 
    for(int i=trail_start; i<=trail_end; i++)
    {
      exprt& trail_exp=graph.prop_trail[i];
      domain.normalize_meetirrd(trail_exp, trail_exp_norm);
      if(expr_norm==trail_exp)
        return i;
      else 
        continue;
    }
  }
  else 
  {
    const exprt &lhs=to_binary_relation_expr(expr_norm).lhs();
    const exprt &rhs=to_binary_relation_expr(expr_norm).rhs();
    for(int i=trail_start; i<=trail_end; i++)
    {
      exprt& trail_exp=graph.prop_trail[i];
      domain.normalize_meetirrd(trail_exp, trail_exp_norm);
      const exprt &lhst=to_binary_relation_expr(trail_exp_norm).lhs();
      const exprt &rhst=to_binary_relation_expr(trail_exp_norm).rhs();
      // match the lhs
      if(lhst == lhs) {
        // check if the types are equal
        if(trail_exp_norm.id() == expr_norm.id())
        {
          // check that new value trail_exp_norm is 
          // a generalization of old value expr_norm
          constant_exprt cexp1=to_constant_expr(rhs);
          constant_exprt cexp2=to_constant_expr(rhst);
          to_integer(cexp1, val1);
          to_integer(cexp2, val2);
          if(expr_norm.id() == ID_ge)
          {
            if(val2<=val1)
              return i;
            else {
              // new value not generalized
              return -1;
            }
          }
          else if(expr_norm.id() == ID_le)
          {
            if(val2>=val1)
              return i;
            else {
              // new value not generalized
              return -1;
            }
          }
        }
      }
      else
        continue;
    }
  }
  // return -1 on failure
  return -1;
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

  for(int i=trail_start; i<=trail_end; i++)
  {
    exprt& trail_exp=graph.prop_trail[i];
    acdl_domaint::varst v_symbol;
    find_symbols(trail_exp, v_symbol);
    for(acdl_domaint::varst::iterator it1=v_symbol.begin(); it1!=v_symbol.end(); it1++) {
      bool is_in=exp_symbols.find(*it1)!=exp_symbols.end();
      if(is_in) {
        bool status=domain.compare(expr, trail_exp);
        if(status==domain.CONFLICT)
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
  unsigned control_point=graph.control_trail.back();
  // traverse from the back of prop_trail, last element is false_exprt
  // since the deduction at the current level leads to conflict,
  // so the deduction are by construction UNSAT
  // so, we need to iterate over all elements explicitly
  // for this segment of propagation trail which corresponds to
  // the current decision level. For other decision levels, we do
  // not need to explicitly traverse the propagation trail segment
  for(unsigned j=graph.prop_trail.size()-1;j>=control_point;j--)
  {
    // std::cout << "The matched expression is: " << from_expr(SSA.ns, "", graph.prop_trail[j]) << std::endl;
    assert(graph.prop_trail[graph.prop_trail.size()-1]==false_exprt());
    // find contradiction by traversing the prop_trail
    // and finding the relevant meet irreducibles
    exprt prop_exp=graph.prop_trail[j];
    acdl_domaint::varst prop_symbols;
    // get symbols from this meet irreducible
    find_symbols(prop_exp, prop_symbols);
    // check if this symbol is in exp_symbols
    for(acdl_domaint::varst::iterator it=prop_symbols.begin(); it!=prop_symbols.end(); it++)
    {
      bool is_in=exp_symbols.find(*it)!=exp_symbols.end();
      if(is_in) {
        // std::cout << "Hey !!! found contradiction with " << from_expr(SSA.ns, "", prop_exp) << std::endl;
        matched_expr.push_back(prop_exp);
        break;
      }
    }
#if 0
    exprt prop_exp=graph.prop_trail[j];
    if(prop_exp!=false_exprt()) {
      std::cout << "The matched expression is: " << from_expr(SSA.ns, "", prop_exp) << std::endl;
      matched_expr.push_back(prop_exp);
    }
#endif
  }
  // push the contradicted literal
  matched_expr.push_back(exp);
  bool status=domain.check_val_satisfaction(matched_expr);
  if(status==0)
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
    unsigned control_trail_size=graph.control_trail.size();
    int search_level=control_trail_size-1;
    while(search_level >= 0) {
      acdl_domaint::valuet val_perdecision;

#ifdef DEBUG
      std::cout << "searching for contradiction at level: " << search_level << std::endl;
#endif
      upper_index=graph.control_trail[search_level];
      if(search_level-1 >= 0)
        lower_index=graph.control_trail[search_level-1];
      else
        lower_index=0;
#ifdef DEBUG
      std::cout << "Upper index is " << upper_index << "lower index is " << lower_index << std::endl;
#endif
      // now traverse the prop_trail
      for(unsigned k=upper_index-1;k>=lower_index;k--) {
        // std::cout << "The matched expression is: " << from_expr(SSA.ns, "", graph.prop_trail[k]) << std::endl;
        assert(k >= 0);
        exprt prop_exp=graph.prop_trail[k];
        val_perdecision.push_back(prop_exp);
        if(k==0) break;
      }
      // assert that the deductions for this decision are consistent
      assert(domain.check_val_consistency(val_perdecision));
      // push the contradicted literal
      val_perdecision.push_back(exp);
      bool status=domain.check_val_satisfaction(val_perdecision);
      if(status==0)
      {
#ifdef DEBUG
        std::cout << "Found contradiction at decision level:" << search_level << "for " << from_expr(SSA.ns, "", exp) << std::endl;
#endif
        return search_level;
      }
      search_level=search_level-1;
    }
  }
  // if the control reaches here, 
  // that means no contradiction 
  // has been found at previous levels
  return 0;
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
  unsigned control_trail_size=graph.control_trail.size();
  unsigned search_level=0;
  while(search_level<=control_trail_size-1) {
    acdl_domaint::valuet val_perdecision;

#ifdef DEBUG
    std::cout << "searching for contradiction at level " << search_level << std::endl;
#endif
    upper_index=graph.control_trail[search_level];
    if(search_level==0)
      lower_index=0;
    else
      lower_index=graph.control_trail[search_level-1];
#ifdef DEBUG
    std::cout << "Upper index is " << upper_index << "lower index is " << lower_index << std::endl;
#endif
    // [TODO] check for empty propagation trail
    if(upper_index==lower_index) {
      search_level=search_level+1;
      continue;
    }
    // now traverse the prop_trail
    for(unsigned k=lower_index;k<=upper_index-1;k++) {
      // std::cout << "The matched expression is: " << from_expr(SSA.ns, "", graph.prop_trail[k]) << std::endl;
      assert(k >= 0);
      exprt prop_exp=graph.prop_trail[k];
      val_perdecision.push_back(prop_exp);
      if(k==upper_index-1) break;
    }
    // assert that the deductions for this decision are consistent
    assert(domain.check_val_consistency(val_perdecision));
    // push the contradicted literal
    val_perdecision.push_back(exp);
    bool status=domain.check_val_satisfaction(val_perdecision);
    if(status==0)
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
  int control_point=graph.control_trail.back();
  // traverse from the back of prop_trail, last element is false_exprt
  // since the deduction at the current level leads to conflict,
  // so the deduction are by construction UNSAT
  // so, we need to iterate over all elements explicitly
  // for this segment of propagation trail which corresponds to
  // the current decision level. For other decision levels, we do
  // not need to explicitly traverse the propagation trail segment
  for(unsigned j=control_point;j<=graph.prop_trail.size()-1;j++)
  {
    // std::cout << "The matched expression is: " << from_expr(SSA.ns, "", graph.prop_trail[j]) << std::endl;
    assert(graph.prop_trail[graph.prop_trail.size()-1]==false_exprt());
    // find contradiction by traversing the prop_trail
    // and finding the relevant meet irreducibles
    exprt prop_exp=graph.prop_trail[j];
    acdl_domaint::varst prop_symbols;
    // get symbols from this meet irreducible
    find_symbols(prop_exp, prop_symbols);
    // check if this symbol is in dec_symbols
    for(acdl_domaint::varst::iterator it=prop_symbols.begin(); it!=prop_symbols.end(); it++)
    {
      bool is_in=exp_symbols.find(*it)!=exp_symbols.end();
      if(is_in) {
        // std::cout << "Hey !!! found contradiction with " << from_expr(SSA.ns, "", prop_exp) << std::endl;
        matched_expr.push_back(prop_exp);
        break;
      }
    }
#if 0
    exprt prop_exp=graph.prop_trail[j];
    if(prop_exp!=false_exprt()) {
      std::cout << "The matched expression is: " << from_expr(SSA.ns, "", prop_exp) << std::endl;
      matched_expr.push_back(prop_exp);
    }
#endif
  }
  // push the contradicted literal
  matched_expr.push_back(exp);
  bool status=domain.check_val_satisfaction(matched_expr);
  if(status==0)
  {
#ifdef DEBUG
    std::cout << "Found contradiction at current decision level for " << from_expr(SSA.ns, "", exp) << std::endl;
#endif
    return graph.current_level;
  }
  // if the control reaches here, 
  // that means no contradiction 
  // has been found at previous levels
  return 0;
}

/*******************************************************************

 Function: acdl_analyze_conflict_baset::preprocess_val()

 Inputs:

 Outputs:

 Purpose: Pre-process abstract value to remove (x==N) constraints 
          by (x<=N) and (x>=N). The trail is not effected by this. 

\*******************************************************************/
void acdl_analyze_conflict_baset::preprocess_val(acdl_domaint::valuet& val)
{
  acdl_domaint::valuet val_temp;
  exprt save_exp;
  for(acdl_domaint::valuet::iterator it=val.begin();it!=val.end(); ++it)
  {
    exprt m=*it;
    if(it->id() == ID_equal)
    {
      save_exp = m;
      std::cout << "Preprocessing value " << from_expr(m) << std::endl;
      exprt &lhs=to_binary_relation_expr(m).lhs();
      exprt &rhs=to_binary_relation_expr(m).rhs();
      // construct x<=N
      exprt expl=binary_relation_exprt(lhs, ID_le, rhs);
      // construct x>=N
      exprt expg=binary_relation_exprt(lhs, ID_ge, rhs);
      // [TODO] erasing causes problem 
      // val.erase(it);
      // val.insert(it, true_exprt());
      val_temp.push_back(expl);
      val_temp.push_back(expg);
      std::cout << "Preprocessing inserted value " << from_expr(expl) << std::endl;
      std::cout << "Preprocessing inserted value " << from_expr(expg) << std::endl;
    }
    else {
      std::cout << "Donot Preprocess value " << from_expr(m) << std::endl;
      continue;
    }
  }
  
  // [TODO] handle if there are multiple equality constraints in val
  val.erase(std::remove(val.begin(), val.end(), save_exp), val.end());
  std::cout << "Now push all collected constraints" << std::endl;
  if(val_temp.size() > 0) 
    val.insert(val.end(), val_temp.begin(), val_temp.end());
}
    
/*******************************************************************

 Function: acdl_analyze_conflict_baset::generalize()

 Inputs:

 Outputs:

 Purpose: Pre-process abstract value to remove (x==N) constraints 
          by (x<=N) and (x>=N). The trail is not effected by this. 

\*******************************************************************/
void acdl_analyze_conflict_baset::generalize(acdl_domaint::valuet& val)
{
#if 0
  // traverse the implication graph from
  // conflict node, and compute the generalization
  // Compute underapproximation by passing target
  // element, transformer, and initial element -- the
  // goal is to compute a weakest initial element that
  // still satisfies the target after the application of
  // the abstract transformer
  acdl_domaint::meet_irreduciblet statement;
  acdl_domaint::varst vars;
  acdl_domaint::valuet init_value;
  acdl_domaint::valuet final_value;
  acdl_domaint::valuet generalized_value;
  // generlize up to a UIP (decision level)
  // For now, we generalize elements in the deepest decision level
  // Input::  init_value ----statement ----> final_value
  // Output:: init_value ----statement ----> generalized_value
  for(unsigned i=reason_trail.size(); i<last_decision_index; i--)
  {
    exprt statement=reason_trail[i].first;
    if(statement!=nil_exprt()) {
      std::pair<unsigned, unsigned> index;
      // construct the abstract final value
      index=reason_trail[i].second;
      unsigned begin=index.first;
      unsigned end=index.second;
      acdl_domaint::valuet val;
      for(unsigned id=begin; id<=end; id++)
        init_value.push_back(conflict_graph.prop_trail[id]);
      // construct the abstract final value
      exprt stmt=conflict_graph.reason_trail[i-1].first;
      if(stmt!=nil_exprt()) {
        index=conflict_graph.reason_trail[i-1].second;
        begin=index.first;
        end=index.second;
        for(unsigned id=begin; id<=end; id++)
          final_value.push_back(conflict_graph.prop_trail[id]);
        domain(statement, vars, init_value, final_value, generalized_value);
        // store the value directly
        // in the propagation trail
      }
    }
    else break;
  }
#endif
}

/*******************************************************************

 Function: acdl_analyze_conflict_baset::dump_section()

 Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/
void acdl_analyze_conflict_baset::dump_section(int begin, int end, acdl_conflict_grapht &graph)
{
  for(int d=begin;d<=end;d++) {
    std::cout << "Trail element is " << from_expr(graph.prop_trail[d]) << std::endl;
  }
  for(int d=begin;d<=end;d++) {
    std::cout << "Reason " << from_expr(graph.reason_trail[d].first) << std::endl;
    std::cout << "Printing propagations through Reason trail index " << std::endl;
    acdl_conflict_grapht::indext index=graph.reason_trail[d].second;
    unsigned begin_index=index.first;
    unsigned end_index=index.second;
    if(begin_index>end_index) 
    {
      std::cout << "Deductions are empty" << std::endl; 
      continue;
    }
    else {
      for(int i=begin_index;i<=end_index;i++) 
        std::cout << "deduction " << from_expr(graph.prop_trail[i]) << std::endl;
      d=d+(end_index-begin_index);
    }
  }
}

/*******************************************************************

 Function: acdl_analyze_conflict_baset::get_reason()

 Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/
void acdl_analyze_conflict_baset::get_reason(
    const local_SSAt &SSA,
    const acdl_domaint::statementt &statement, 
    const acdl_domaint::valuet &init_value,
    const acdl_domaint::valuet &final_value,
    acdl_domaint::valuet &reason)
{
  acdl_domaint::valuet v;
  acdl_domaint::varst stmt_symbols;
  // get symbols from this meet irreducible
  find_symbols(statement, stmt_symbols);
  // Collect the meet irreducibles
  // in init_value that has same symbols as the 
  // statement that lead to final_value
/*  for(acdl_domaint::valuet::const_iterator it=init_value.end();
      it!=init_value.begin();it--) */
  for(unsigned i=init_value.size()-1;i>=0;i--)
  {
    exprt trail_exp=init_value[i];
#ifdef DEBUG
    std::cout << "The meet irreducible checked is " 
      << from_expr(trail_exp) << std::endl;
#endif
    assert(trail_exp != false_exprt());
    acdl_domaint::varst prop_symbols;
    // get symbols from this meet irreducible
    find_symbols(trail_exp, prop_symbols);
    // check if this symbol is in stmt_symbols
    for(acdl_domaint::varst::iterator it=prop_symbols.begin(); it!=prop_symbols.end(); it++)
    {
      bool is_in=stmt_symbols.find(*it)!=stmt_symbols.end();
      if(is_in) {
#ifdef DEBUG
        std::cout << "Found matching symbols, put " 
          << from_expr(trail_exp) << " into array" << std::endl;
#endif
        // [TODO] Do we normalize the expression before inserting ?
        v.push_back(trail_exp);
      }
    }
    if(i==0) break;
  }
  
  assert(v.size() > 0);
  std::cout << "HERE" << std::endl;
/*#ifdef DEBUG
  std::cout << "Checking that the relevant value " 
    << from_expr(conjunction(v)) << "is the reason for the final value when the transformer "
    << from_expr(statement) << "is applied" << std::endl;
#endif*/

  std::unique_ptr<incremental_solvert> solver(
      incremental_solvert::allocate(SSA.ns, true));
  *solver << implies_exprt(conjunction(final_value), and_exprt(statement,conjunction(v)));
  decision_proceduret::resultt result=(*solver)();
  if(result==decision_proceduret::D_SATISFIABLE) {
#ifdef DEBUG
    std::cout << "The value " << from_expr(conjunction(v))
      << "is the reason for deriving " 
      << from_expr(conjunction(final_value)) << std::endl;
#endif
  }
#ifdef DEBUG
  std::cout << "The initial reason is " << std::endl;
  for(unsigned j=0;j<v.size();j++)
    std::cout << "Reason element:: " << from_expr(v[j]) << std::endl;
#endif
}
