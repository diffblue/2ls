/*******************************************************************\

Module: ACDL Solver

Author: Rajdeep Mukherjee, Peter Schrammel

\*******************************************************************/


#include <langapi/language_util.h>
#include <util/simplify_expr.h>
#include <util/find_symbols.h>
#include "acdl_solver.h"
#include "acdl_domain.h"
#include <domains/simplify_transformer.h>
#include <string>
#include <iostream>

#define DEBUG
// #define PER_STATEMENT_LIVE_VAR
#define LIVE_VAR_OLD_APPROACH

/*******************************************************************

 Function: acdl_solvert::propagate()

 Inputs:

 Outputs:

 Purpose: Parent module for propagation :
           a> Propagation at clause level
           b> Propagation at SSA level

\*******************************************************************/
property_checkert::resultt acdl_solvert::propagate
(const local_SSAt &SSA, const exprt &assertion)
{
  bool conflict=!deduce(SSA);
  analyzes_conflict.last_proof=analyzes_conflict.PROPOSITIONAL;
  if(!conflict) {
    std::cout << "Propagation did not lead to CONFLICT in propositional clauses !!" << std::endl;
    std::cout << "Starting propagation using AI: forward and backward iteration" << std::endl;
    return propagation(SSA, assertion);
  }
  return property_checkert::UNKNOWN;
}

/*******************************************************************

 Function: acdl_solvert::deduce()

 Inputs:

 Outputs:

 Purpose: Propagate information using the learnt clause.
          checks whether the CONFLICT is due to learned_clauses,
          that is whether the conflict is purely PROPOSITIONAL

\*******************************************************************/
bool acdl_solvert::deduce(const local_SSAt &SSA)
{
  std::cout << "Starting Propagation in Propositional clauses" << std::endl;
  // assert(analyzes_conflict.learned_clauses.size()!=0);
  // iterate over all new elements in the prop_trail obtained from decision
  // or backtracking and check if any new deductions can be inferred from the
  // learnt clause by applying UNIT rule
  for( ;analyzes_conflict.bcp_queue_top<conflict_graph.prop_trail.size(); analyzes_conflict.bcp_queue_top++) {
    // if bcp fails, then a clause is CONFLICTING
    if(!bcp(SSA, analyzes_conflict.bcp_queue_top))
      return false;
  }
  return true;
}

/*******************************************************************

 Function: acdl_solvert::bcp()

 Inputs:

 Outputs:

 Purpose: only needed for non-chronological backtracking

\*******************************************************************/
bool acdl_solvert::bcp(const local_SSAt &SSA, unsigned idx)
{
#if 0

  // **********************************************
  Finding phase of a meet irreducible:
    cdfpl implementation apply unit rule to clauses whose meet
    irreducibles are of same phase as that of the meet
    irreducible in the propagation trail.
    Example: Meet irreducibles in the trail: x>5, y<20, z>5
    Clause: (x<3 V y>50 V z<10)
    Clearly, the phase of variable z is different,
    (z>18) and (z<10). But, application of unit rule
    still deduces (z<10). So, we donot check for phase.
    // **********************************************

    assert(idx!=0);

  exprt exp=conflict_graph.prop_trail[idx];
  acdl_domaint::varst exp_symbol;
  // get symbols from this meet irreducible
  find_symbols(exp, exp_symbol);
  analyzes_conflict.conflicting_clause=-1;

  // find previous assignment to same variable
  int prev_idx=idx-1;
  for(;prev_idx > 0; prev_idx--) {
    exprt prv_exp=conflict_graph.prop_trail[prev_idx];
    acdl_domaint::varst prv_exp_symbol;
    // get symbols from this meet irreducible
    find_symbols(prv_exp, prv_exp_symbol);
    for(acdl_domaint::varst::iterator it=prv_exp_symbol.begin(); it!=prv_exp_symbol.end(); it++) {
      bool is_in=exp_symbol.find(*it)!=exp_symbol.end();
      if(is_in) break;
    }
  }
  // there must be a previous assignment
  assert(prev_idx >= 0);

#endif

  unsigned i=0;
#ifdef DEBUG
  std::cout << "The size of learned clauses is " << analyzes_conflict.learned_clauses.size() << std::endl;
#endif
  while(i<analyzes_conflict.learned_clauses.size()) {
    // note that each application of unit rule
    // may infer new deductions, so we compute
    // the new abstract value everytime
    exprt unit_lit;
    acdl_domaint::valuet v;
    conflict_graph.to_value(v);

    // preprocess abstract value: 
    // transform constraints like 
    // (x==n) to (x<=n) and (x>=n)
    preprocess_val(v);
#ifdef debug
    std::cout << "preprocessed abstract value of implication graph: " << std::endl;
    for(acdl_domaint::valuet::const_iterator it=v.begin();it!=v.end(); ++it)
      std::cout << from_expr(ssa.ns, "", *it) << std::endl;
#endif

    acdl_domaint::valuet clause_val=analyzes_conflict.learned_clauses[i];
    int result=domain.unit_rule(SSA, v, clause_val, unit_lit);
#ifdef DEBUG
    std::cout << "The propagation from unit rule inside bcp is " << from_expr(SSA.ns, "", unit_lit) << std::endl;
#endif
    if(result==domain.CONFLICT) {
      analyzes_conflict.conflicting_clause=i;
      analyzes_conflict.last_proof=analyzes_conflict.PROPOSITIONAL;
      std::cout << "Propagation in Propositional clauses lead to conflict" << std::endl;
      return false; // if conflict, return false
    }
    else if(result==domain.UNIT) {
      // we need to take a meet of the
      // unit literal and the abstract value
      // the effect of taking meet can also be
      // achieved by pushing it into the graph
      std::cout << "Propagation in Propositional clauses is UNIT" << std::endl;
      conflict_graph.assign(unit_lit);
    }
    i++;
  }
  return true;
}

/*******************************************************************\

Function: acdl_solvert::propagation

 Inputs: Chaotic propagation -- forward and backward

 Outputs:

 Purpose: Worklist algorithm sketch
 list<statementt> worklist;
 valuet v=true_exprt();
 // Initialize worklist
 // wl <-- first_statement in localSSA.nodes;
 do {
  s=worklist_pop();
  post(s, v); // this will update v
  // Find statements where s.lhs appears in RHS of SSA nodes, insert the whole statement in worklist
  // To do this, iterate over the localSSA.nodes and collect all these statements
   populate_worklist(s.lhs);
 } while(worklist!=0);

 In ACDCL, we do gfp computation, so we start with TOP and perform
 forward abstract analysis to compute the post-condition of a statement
\************************************************************************/

property_checkert::resultt acdl_solvert::propagation(const local_SSAt &SSA, const exprt &assertion)
{
  //unsigned init_size=conflict_graph.prop_trail.size();
  acdl_domaint::valuet final_val;
  while (!worklist.empty())
  {
    const acdl_domaint::statementt statement=worklist.pop();

#if 0  
    // MUST NOT DO THE OPTIMIZATION BELOW SINCE THIS CAN 
    // BLOCK SOME RELEVANT DEDUCTIONS. For example, if domain=octagon 
    // and assumption x==y, then it can not derive any fact since
    // there is no way to represent equality (==) in octagons 
    // [OPTIMIZATION] do not process the assumption statements
    // since they are already explicitly added to the trail
    std::vector<acdl_domaint::statementt>::iterator ita;
    ita = find (assume_statements.begin(), assume_statements.end(), statement);
    if (ita != assume_statements.end())
      continue;
#endif

    acdl_domaint::varst lvar;
#ifdef PER_STATEMENT_LIVE_VAR
    lvar=worklist.pop_from_map(statement);
#endif

#ifdef DEBUG
    std::cout << "Pop: " << from_expr (SSA.ns, "", statement)
              << std::endl;
#endif

#ifdef DEBUG
#ifdef PER_STATEMENT_LIVE_VAR
    std::cout << "Live variables for " << from_expr(statement) << " are: ";
    for(acdl_domaint::varst::const_iterator it1=
          lvar.begin(); it1!=lvar.end(); ++it1)
      std::cout << from_expr(*it1) << ", ";
    std::cout << std::endl;
#endif
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
    // domain.normalize_val(v);

    // preprocess abstract value 
    // transform constraints like (x==N) to (x<=N) and (x>=N)
    preprocess_val(v);
#ifdef DEBUG
    std::cout << "Computing preprocessed abstract value of implication graph: " << std::endl;
    for(acdl_domaint::valuet::const_iterator it=v.begin();it!=v.end(); ++it)
      std::cout << from_expr(SSA.ns, "", *it) << std::endl;
#endif

#ifdef DEBUG
    std::cout << "Computing old abstract value of implication graph: " << std::endl;
    for(acdl_domaint::valuet::const_iterator it=v.begin();it!=v.end(); ++it)
      std::cout << from_expr(SSA.ns, "", *it) << std::endl;
#endif

#ifdef DEBUG
    std::cout << "Old: ";
    domain.output(std::cout, v) << std::endl;
#endif

    
    // select vars for projection
    acdl_domaint::valuet new_v;
    acdl_domaint::varst project_vars;
    acdl_domaint::varst projected_live_vars;
#ifdef LIVE_VAR_OLD_APPROACH
    find_symbols(statement, project_vars);
    projected_live_vars=worklist.check_var_liveness(project_vars);
#endif

    // do path-sensitive analysis
    // for efficient gamma-complete check
    find_symbols(statement, project_vars);
    acdl_domaint::varst gvar;
    if(statement.id()==ID_equal) {
      exprt expr_rhs=to_equal_expr(statement).rhs();
      if(expr_rhs.id()==ID_if) {
        // insert the statement into map
        // so that we do not compute the
        // non-gamma-complete variables for
        // the statement the next time it
        // is popped. Note that a statement
        // can be popped multiple times in a
        // chaotic iteration to reach fixed-point
        std::set<acdl_domaint::statementt>::iterator itf;
        itf=gamma_check_processed.find(statement);
        if(itf!=gamma_check_processed.end()) goto DEDUCE;
        else {
          gamma_check_processed.insert(statement);
          exprt exp=expr_rhs.op0();
#ifdef DEBUG
          std::cout << "Original Gamma statement: " << from_expr(statement) << "op0: " << from_expr(exp) << std::endl;
#endif
          // now check if op0 is already
          // concrete in the abstract value
          acdl_domaint::valuet::const_iterator i_op1;
          acdl_domaint::valuet::const_iterator i_op2;
          i_op1=find(v.begin(), v.end(), exp);
          i_op2=find(v.begin(), v.end(), not_exprt(exp));
          if(i_op1!=v.end() || i_op2!=v.end()) {
            exprt sexp;
            exprt s=statement;
            if(i_op1!=v.end()) {
              replace_expr(exp, true_exprt(), s);
#ifdef DEBUG
              std::cout << "Replaced statement " << from_expr(s) << std::endl;
#endif
              sexp=simplify_expr(s, SSA.ns);
            }
            if(i_op2!=v.end()) {
              replace_expr(exp, false_exprt(), s);
#ifdef DEBUG
              std::cout << "Replaced statement " << from_expr(s) << std::endl;
#endif
              sexp=simplify_expr(s, SSA.ns);
            }
#ifdef DEBUG
            std::cout << "Original statement: " << from_expr(statement) << "Simplified statement: " << from_expr(sexp) << std::endl;
#endif
            acdl_domaint::varst p_vars;
            // find variables in current statement that
            // exist in the projected_live_vars
#ifdef LIVE_VAR_OLD_APPROACH
            set_intersection(projected_live_vars.begin(), projected_live_vars.end(),
                             project_vars.begin(), project_vars.end(), std::inserter(p_vars, p_vars.begin()));
            find_symbols(sexp, gvar);
            std::set_difference(p_vars.begin(), p_vars.end(), gvar.begin(), gvar.end(),
                                std::inserter(non_gamma_complete_var, non_gamma_complete_var.end()));
#endif

#ifdef PER_STATEMENT_LIVE_VAR
            find_symbols(sexp, gvar);
            std::set_difference(lvar.begin(), lvar.end(), gvar.begin(), gvar.end(),
                                std::inserter(non_gamma_complete_var, non_gamma_complete_var.end()));
#endif
          }
        } // not seen the statement before
      }
    }
  DEDUCE:
#ifdef LIVE_VAR_OLD_APPROACH
#ifdef DEBUG
    std::cout << "The list of live variables are " << std::endl;
    for(acdl_domaint::varst::const_iterator it=projected_live_vars.begin();it!=projected_live_vars.end(); ++it)
      std::cout << from_expr(SSA.ns, "", *it) << std::endl;
    if(gvar.size() > 0) {
      std::cout << "The list of variables in simplified statement are " << std::endl;
      for(acdl_domaint::varst::const_iterator t=gvar.begin(); t!=gvar.end(); ++t)
        std::cout << from_expr(SSA.ns, "", *t) << std::endl;
    }
    if(non_gamma_complete_var.size() > 0) {
      std::cout << "The list of non-gamma complete variables are " << std::endl;
      for(acdl_domaint::varst::const_iterator ng=non_gamma_complete_var.begin();ng!=non_gamma_complete_var.end(); ++ng)
        std::cout << from_expr(SSA.ns, "", *ng) << std::endl;
    }
#endif
#endif

#ifdef LIVE_VAR_OLD_APPROACH
    domain(statement, projected_live_vars, v, new_v, deductions);
#endif

    // [QUERY] find intersection of project_vars and lvar
    // for per-statement based live variable approach
    // set_intersection(lvar.begin(), lvar.end(), project_vars.begin(), project_vars.end(), std::inserter(projected_live_vars, projected_live_vars.begin()));

#ifdef PER_STATEMENT_LIVE_VAR
    domain(statement, lvar, v, new_v, deductions);
#endif

    // update implication graph
    conflict_graph.add_deductions(SSA, deductions, statement);
    propagations++;
    // update worklist based on variables in the consequent (new_v)
    // -collect variables in new_v
    acdl_domaint::varst new_variables;
    for(acdl_domaint::valuet::const_iterator
          it1=new_v.begin(); it1!=new_v.end(); ++it1)
      find_symbols(*it1, new_variables);

    // -call worklist update
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
    // implication_graph.to_value(new_v);
    conflict_graph.to_value(new_v);


    // preprocess abstract value: 
    // transform constraints like 
    // (x==n) to (x<=n) and (x>=n)
    preprocess_val(new_v);
#ifdef debug
    std::cout << "preprocessed abstract value of implication graph: " << std::endl;
    for(acdl_domaint::valuet::const_iterator it=new_v.begin();it!=new_v.end(); ++it)
      std::cout << from_expr(ssa.ns, "", *it) << std::endl;
#endif


    final_val=new_v;
#ifdef DEBUG
    std::cout << "Computing new abstract value of implication graph: " << std::endl;
    for(acdl_domaint::valuet::const_iterator it=new_v.begin();it!=new_v.end(); ++it)
      std::cout << from_expr(SSA.ns, "", *it) << std::endl;
#endif

    // Cool! We got UNSAT
    // domain.normalize(new_v, projected_live_vars);
    domain.normalize(new_v);
    if(domain.is_bottom(new_v))
    {
#ifdef DEBUG
      std::cout << "Propagation finished with BOTTOM" << std::endl;
#endif
#ifdef PER_STATEMENT_LIVE_VAR
      // empty the map
      worklist.delete_map();
#endif
      // empty the worklist because the present deduction
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
      analyzes_conflict.last_proof=analyzes_conflict.ABSINT;
      return property_checkert::PASS; // potential UNSAT (modulo decisions)
    }
  }

  // [TODO] check if new_v is EMPTY,
  // that is no propagation has been made,
  // this can only happen in first deduction phase
  // because in subsequent deduction levels new_v
  // will atleast contain old_v and is not EMPTY
  if(final_val.empty()) {
#ifdef DEBUG
    std::cout << "Empty deduction, so inserting TRUE" << std::endl;
#endif
    std::vector<acdl_domaint::meet_irreduciblet> ded;
    exprt e=true_exprt();
    ded.push_back(e);
    conflict_graph.add_deductions(SSA, ded, false_exprt());
  }
  //unsigned final_size=conflict_graph.prop_trail.size();
  // propagations=propagations+(final_size-init_size);

  // [SPECIAL CHECK] explicitly empty the map here when we
  // do not delete map elements for
  // statements with empty deductions
  // Only activate the check -- when missing some deductions,
  // do not delete map elements for empty deduction in
  // update function in worklist_base (comment out top check)
  // #if 0
  // worklist.delete_map();
  // #endif
#if 0
  // if there are no deductions, then
  // remove the last decision from the
  // decision_trail as well decrease the
  // decision_level
  if(final_size-init_size==0) {
    std::cout << "No propagations possible from this decision, so cancel the trail once !!" << std::endl;
    dec_not_in_trail.push_back(conflict_graph.dec_trail.back());
    analyzes_conflict.cancel_once(SSA, conflict_graph);
  }
#endif
  // check for closed abstract value
  std::cout<< "***** CLOSURE Check ******" << std::endl;
  bool status = is_closed(SSA, final_val);
  if(status) 
    std::cout << "The abstract value is closed" << std::endl;
  else {
    std::cout << "The abstract value is not closed" << std::endl;
    assert(0);
  }

#ifdef DEBUG
  std::cout << "Propagation finished with UNKNOWN" << std::endl;
#endif
  return property_checkert::UNKNOWN;
}

/*******************************************************************

 Function: acdl_solvert::preprocess_val()

 Inputs:

 Outputs:

 Purpose: Pre-process abstract value to remove (x==N) constraints 
          by (x<=N) and (x>=N). The trail is not effected by this. 

\*******************************************************************/
void acdl_solvert::preprocess_val(acdl_domaint::valuet& val)
{
  acdl_domaint::valuet val_temp;
  std::vector<exprt> save_exp;
  for(acdl_domaint::valuet::iterator it=val.begin();it!=val.end(); ++it)
  {
    exprt m=*it;
    if(it->id() == ID_equal)
    {
      save_exp.push_back(m);
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
  for(std::vector<exprt>::iterator it=save_exp.begin(); it!=save_exp.end(); it++)
    val.erase(std::remove(val.begin(), val.end(), *it), val.end());
    //val.erase(std::remove(val.begin(), val.end(), save_exp), val.end());
  std::cout << "Now push all collected constraints" << std::endl;
  if(val_temp.size() > 0) 
    val.insert(val.end(), val_temp.begin(), val_temp.end());
}

/*******************************************************************

 Function: acdl_solvert::is_closed()

 Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
bool acdl_solvert::is_closed(const local_SSAt &SSA, acdl_domaint::valuet& val)
{
  acdl_domaint::valuet new_val;
  acdl_domaint::deductionst deductions;
  domain(true_exprt(), all_vars, val, new_val, deductions);
#ifdef DEBUG
    std::cout << "Old Abstract Value for Closure: " << std::endl;
    for(acdl_domaint::valuet::const_iterator itv=val.begin();
        itv!=val.end(); ++itv)
      std::cout << from_expr(SSA.ns, "", *itv) << std::endl;
    
    std::cout << "New Abstract Value for Closure: " << std::endl;
    for(acdl_domaint::valuet::const_iterator itn=new_val.begin();
        itn!=new_val.end(); ++itn)
      std::cout << from_expr(SSA.ns, "", *itn) << std::endl;
#endif
  // compare val and new_val
  domain.normalize(val);
  domain.normalize(new_val);
#ifdef DEBUG
    std::cout << "Old Normalized Abstract Value: " << std::endl;
    for(acdl_domaint::valuet::const_iterator itv=val.begin();
        itv!=val.end(); ++itv)
      std::cout << from_expr(SSA.ns, "", *itv) << std::endl;
    
    std::cout << "New Normalized Abstract Value: " << std::endl;
    for(acdl_domaint::valuet::const_iterator itn=new_val.begin();
        itn!=new_val.end(); ++itn)
      std::cout << from_expr(SSA.ns, "", *itn) << std::endl;
#endif


  // check if all meet irreducibles in 
  // new_val is subsumed in val
  for(acdl_domaint::valuet::iterator it=new_val.begin();
      it!=new_val.end();++it)
  {
    acdl_domaint::valuet::iterator it1=find(val.begin(), val.end(), *it);
    if(!(domain.is_subsumed(*it, val))) {
        //return false;
       if(it1 == val.end()) {
         std::cout << "The meet irreducible " << from_expr(*it1) << 
           " is neither subsumed nor present in the old normalized value" << std::endl; 
        return false;
       }
       // [CHECK] Not sure if the following situation can occur ?
       else {
         std::cout << "The meet irreducible " << from_expr(*it1) << 
           " is not subsumed but present in the old normalized value" << std::endl; 
         continue;
       }
    }
    else
        continue;
  }
  std::cout << "The abstract value is closed " << std::endl;
  return true;
}

/*******************************************************************

 Function: acdl_solvert::decide()

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

bool acdl_solvert::decide (const local_SSAt &SSA, const exprt& assertion)
{
  decisions++;
  // When a new decision is made, the
  // live variable set must be flushed
  worklist.delete_map();
  worklist.live_variables.erase
    (worklist.live_variables.begin(), worklist.live_variables.end());

  acdl_domaint::valuet v;
  conflict_graph.to_value(v);

  // preprocess abstract value: 
  // transform constraints like 
  // (x==n) to (x<=n) and (x>=n)
  preprocess_val(v);
#ifdef debug
  std::cout << "preprocessed abstract value of implication graph: " << std::endl;
  for(acdl_domaint::valuet::const_iterator it=v.begin();it!=v.end(); ++it)
    std::cout << from_expr(ssa.ns, "", *it) << std::endl;
#endif

  acdl_domaint::valuet old_v;
  conflict_graph.to_value(old_v);
  
  // preprocess abstract value: 
  // transform constraints like 
  // (x==n) to (x<=n) and (x>=n)
  preprocess_val(old_v);
#ifdef debug
  std::cout << "preprocessed abstract value of implication graph: " << std::endl;
  for(acdl_domaint::valuet::const_iterator it=old_v.begin();it!=old_v.end(); ++it)
    std::cout << from_expr(ssa.ns, "", *it) << std::endl;
#endif

#ifdef DEBUG
  std::cout << "Checking consistency of trail before adding decision" << std::endl;
#endif
  assert(domain.check_val_consistency(v));
#ifdef DEBUG
  std::cout << "Trail is consistent" << std::endl;
#endif

#if 0
  // Add the decisions that did not contribute
  // to any deductions here since such
  // information is not in the trail
  for(int i=0;i<dec_not_in_trail.size();i++)
    v.push_back(dec_not_in_trail[i]);
#endif

  // Normalizing here is absolute must
  // Otherwise, unsafe cases does not terminate
  domain.normalize_val(v);
  acdl_domaint::meet_irreduciblet dec_expr=decision_heuristics(SSA, v);
  if(dec_expr==false_exprt())
    return false;
  std::cout << "The decision expression is " << from_expr(dec_expr) << std::endl;
  // test to check if a decision is valid
  // wrt. the current value, this check happens
  // inside decision_heuristic, so redundant here
  bool valid_decision=true;
  old_v.push_back(dec_expr);
  if(!domain.check_val_consistency(old_v)) {
    std::cout << "The trail is inconsistent after adding decision, so get new decision" << std::endl;
    std::cout << "The inconsistent trail is " << from_expr(conjunction(old_v)) << std::endl;
    /*while(valid_decision) {
      dec_expr=decision_heuristics(SSA, v);
      // no new decisions can be made
      if(dec_expr==false_exprt())
        return false;
      std::cout << "Iterate: The decision expression is " << from_expr(dec_expr) << std::endl;
      std::cout << "Checking consistency of decision wrt. current value" << std::endl;
      old_v.push_back(dec_expr);
      std::cout << "The last pushed element is " << from_expr(old_v.back()) << std::endl;
      std::cout << "The content of appended value is " << std::endl;
      domain.output(std::cout, old_v) << std::endl;
      if(domain.check_val_consistency(old_v)) {
        valid_decision=false;
        old_v.pop_back();
        std::cout << "The value is consistent, found a new decison thorugh ITERATION !! " << std::endl;
        break;
      }
      else {
        std::cout << "The last popped element is " << from_expr(old_v.back()) << std::endl;
        std::cout << "The trail is inconsistent after adding decision, so get new decision" << std::endl;
        std::cout << "The inconsistent trail is " << from_expr(conjunction(old_v)) << std::endl;
        old_v.pop_back();
        continue;
      }
    }*/
  }

  // *****************************************************************
  // 1.b. e.g. we have x!=2 in an assertion or cond node, then we have
  // meet irreducibles x<=1, x>=3 as potential decisions
  // ****************************************************************


  // ****************************
  // 2. call acdl_domaint::split
  // ****************************
#if 0
  std::cout << "DECISION PHASE: " << from_expr (SSA.ns, "", alist.front()) << std::endl;
  decision=domain.split(alist.front(), decision_expr);
#endif

  // update conflict graph
  conflict_graph.add_decision(dec_expr);
  // save the last decision index
  last_decision_index=conflict_graph.prop_trail.size();
  // check that the meet_ireducibles in the prop trail
  // is consistent after adding every decision. The value
  // should not lead to UNSAT
  // (that is, there must not be x>0, x<0
  // at the same time in the trail)
  acdl_domaint::valuet new_value;
  conflict_graph.to_value(new_value);
  
  // preprocess abstract value: 
  // transform constraints like 
  // (x==n) to (x<=n) and (x>=n)
  preprocess_val(new_value);
#ifdef debug
  std::cout << "preprocessed abstract value of implication graph: " << std::endl;
  for(acdl_domaint::valuet::const_iterator it=new_value.begin();it!=new_value.end(); ++it)
    std::cout << from_expr(ssa.ns, "", *it) << std::endl;
#endif

  std::cout << "Checking consistency of trail after adding decision" << std::endl;
  assert(domain.check_val_consistency(new_value));
  std::cout << "Trail is consistent" << std::endl;

#ifdef DEBUG
  std::cout << "FINAL DECISION: " << from_expr (SSA.ns, "", dec_expr) << std::endl;
#endif

  // Take meet of the decision expression (decision)
  // with the current abstract state (v).
  // The new abstract state is now in v
  domain.meet(dec_expr, v);

#ifdef DEBUG
  std::cout << "Before normalize: " << std::endl;
  domain.output(std::cout, v) << std::endl;
#endif

  // normalize v
  domain.normalize_val(v);

#ifdef DEBUG
  std::cout << "New: ";
  domain.output(std::cout, v) << std::endl;
#endif

#if 0
  // access the decision statement associated
  // with the chosen decision variables
  acdl_domaint::statementt dec_stmt=decision_heuristics.dec_statement;

  acdl_domaint::varst dec_vars;
  // find all symbols in the decision expression
  find_symbols(dec_stmt, dec_vars);

  // initialize the worklist here with all
  // transitive dependencies of the decision
  // worklist.dec_update(SSA, dec_stmt);
#endif

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
  learning++;
  if(!analyzes_conflict(SSA, conflict_graph)) {
    return false;
  }
  else {
    if(analyzes_conflict.disable_backjumping) {
      acdl_domaint::valuet v;
      conflict_graph.to_value(v);

      // preprocess abstract value: 
      // transform constraints like 
      // (x==n) to (x<=n) and (x>=n)
      preprocess_val(v);
#ifdef debug
      std::cout << "preprocessed abstract value of implication graph: " << std::endl;
      for(acdl_domaint::valuet::const_iterator it=v.begin();it!=v.end(); ++it)
        std::cout << from_expr(ssa.ns, "", *it) << std::endl;
#endif

      // call normalize or normalize_val ?
      domain.normalize_val(v);
      exprt dec_expr=conflict_graph.prop_trail.back();
      domain.meet(dec_expr, v);
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
      // no need to push learned clause into the worklist
      // since the propagation stage must infer information
      // from learned clause
      acdl_domaint::valuet learned_clause;
      learned_clause=analyzes_conflict.learned_clauses.back();

      // the learnt clause looks like (!D1 || !D2 || !UIP)
      const exprt learned_expr=disjunction(learned_clause);
      acdl_domaint::statementt learned_stmt=learned_expr;
      // update the worklist based on all transitively
      // dependant elements of the learnt clause
      worklist.dec_update(SSA, learned_stmt, assertion);
      return true;
    }
  }
}

/*******************************************************************

 Function: acdl_solvert::generalize_proof()

 Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
void acdl_solvert::generalize_proof(const local_SSAt &SSA, const exprt& assertion, acdl_domaint::valuet& val) const
{
  if(disable_generalization || analyzes_conflict.disable_backjumping)
    return;
#ifdef DEBUG
  std::cout << "Generalizing proof !" << std::endl;
#endif
  // generalize only when the conflict is due to AI proof
  if(analyzes_conflict.last_proof==analyzes_conflict.ABSINT) {
    assert(analyzes_conflict.conflicting_clause==-1);
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
    // For now, we generalize up to last decision level
    // Input::  init_value ----statement ----> final_value
    // Output:: init_value ----statement ----> generalized_value
    for(unsigned i=conflict_graph.reason_trail.size(); i<last_decision_index; i--)
    {
      exprt statement=conflict_graph.reason_trail[i].first;
      if(statement!=nil_exprt()) {
        std::pair<unsigned, unsigned> index;
        // construct the abstract initial value
        index=conflict_graph.reason_trail[i].second;
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
  }
}

/*******************************************************************

 Function: acdl_solvert::init()

 Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
void acdl_solvert::init()
{
  // initialize bcp_queue_top
  analyzes_conflict.bcp_queue_top=0;

  // iterate over all vars
  for(std::set<symbol_exprt>::iterator it=all_vars.begin();
      it!=all_vars.end();it++)
  {
    // number all symbol_exprts
    unsigned nr=conflict_graph.numbering_symbol.number(to_symbol_expr(*it));
    assert(nr==conflict_graph.values.size());
    std::pair<int, int> intv;
    intv.first=-99999;
    intv.second=-99999;
    conflict_graph.values.push_back(intv);
  }
}

/*******************************************************************

 Function: acdl_solvert::initialize_decision_variable()

 Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
void acdl_solvert::initialize_decision_variables(acdl_domaint::valuet &value)
{
  for(std::set<exprt>::const_iterator
        it=decision_heuristics.decision_variables.begin();
      it!=decision_heuristics.decision_variables.end(); ++it)
  {
    std::pair<mp_integer, mp_integer> val_itv;
    val_itv=domain.get_var_bound(value, *it);
    decision_heuristics.initialize_decvar_val(val_itv);
  }
}

/*******************************************************************

 Function: acdl_solvert::print_solver_statistics()

 Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
void acdl_solvert::print_solver_statistics()
{
  std::cout << "********************************" << std::endl;
  std::cout << "Printing ACDL Solver Statistics" << std::endl;
  std::cout << "********************************" << std::endl;
  std::cout << "Decisions:: " << decisions << std::endl;
  std::cout << "Learning Iterations:: " << learning << std::endl;
  std::cout << "Learnt clauses:: " << analyzes_conflict.learned_clauses.size() << std::endl;
  std::cout << "Learnt literals:: " << learned_literals << std::endl;
  std::cout << "Propagation::" << propagations << std::endl;
}

/*******************************************************************

 Function: acdl_solvert::pre_process()

 Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
void acdl_solvert::pre_process (const local_SSAt &SSA, const exprt &assertion, const exprt &assumption)
{
  std::cout << "********************************" << std::endl;
  std::cout << "Pre-processing SSA" << std::endl;
  std::cout << "********************************" << std::endl;

  find_symbols_sett var_set;
  typedef std::set<irep_idt> var_stringt;
  var_stringt var_string;
  typedef std::vector<acdl_domaint::statementt> conjunct_listt;
  conjunct_listt clist;
  std::set<exprt> var_lhs;
  acdl_domaint::varst sym_lhs;
  std::string str("nondet");
  
  typedef std::vector<exprt> enable_exprt;
  enable_exprt enable_expr;
#ifdef DEBUG
  std::cout << "Printing the SSA enabling expression:: " << from_expr(SSA.get_enabling_exprs()) << std::endl;
#endif
  // collect the enabling expressions of SSA
  enable_expr=SSA.get_enabling_exprs().operands();

  if (SSA.nodes.empty ())
    return;
  for (local_SSAt::nodest::const_iterator n_it=SSA.nodes.begin ();
       n_it!=SSA.nodes.end (); n_it++)
  {
    // Process nodes with valid SSA expressions
    // For example, if SSA enabling_expr=!enable0 && enable1,
    // then all nodes with enabling expression as enable0 is invalid
    // and only nodes with enabling expression as enable1 is valid
    // Nodes with enabling expression as true is always valid
    // n_it->enabling_expr==true_exprt() -- valid node
#ifdef DEBUG
    std::cout << "The enabling expr of node is " << from_expr(n_it->enabling_expr) << std::endl;
#endif
    exprt exp_en=n_it->enabling_expr;
    // check if negation of exp_en matches with
    // any of the entries in the vector enable_expr
    exprt search_expr=not_exprt(exp_en);
    std::vector<exprt>::iterator it_en;
    it_en=find(enable_expr.begin(), enable_expr.end(), search_expr);
    if(exp_en!=true_exprt()) {
      if(it_en!=enable_expr.end())
        continue;
    }

#ifdef DEBUG
    std::cout << "The enabling expr of valid node is " << from_expr(n_it->enabling_expr) << std::endl;
#endif
    for (local_SSAt::nodet::equalitiest::const_iterator e_it=
           n_it->equalities.begin (); e_it!=n_it->equalities.end (); e_it++)
    {
      clist.push_back(*e_it);
#ifdef DEBUG
      std::cout << "The statement pushed is " << from_expr(*e_it) << std::endl;
#endif
      // find all leaf variables
      acdl_domaint::varst leaf_vars;
      if(e_it->id()==ID_equal) {
        exprt expr_rhs=to_equal_expr(*e_it).rhs();
        if(expr_rhs.id()==ID_constant || expr_rhs.is_true() || expr_rhs.is_false()) {
          // DONOT pass variables with constants
          // in rhs to simplify_transformer
          // find_symbols(*e_it, var_set);
        }
        else {
          exprt expr_rhs=to_equal_expr(*e_it).rhs();
          std::string str("nondet");
          std::string rhs_str=id2string(expr_rhs.get(ID_identifier));
          std::size_t found=rhs_str.find(str);
          if(found!=std::string::npos) {
            find_symbols(*e_it, var_set);
            // collect all read-only symbols of equality
            exprt exprl=to_equal_expr(*e_it).lhs();
            find_symbols(exprl, var_lhs);
            find_symbols(exprl, sym_lhs);
            read_only_vars.insert(var_lhs.begin(), var_lhs.end());
            read_only_symbols.insert(sym_lhs.begin(), sym_lhs.end());
          }
          // collect conditional variables
          exprt expr_lhs=to_equal_expr(*e_it).lhs();
          std::string strl("cond#");
          std::string lhs_str=id2string(expr_lhs.get(ID_identifier));
          std::size_t f=lhs_str.find(strl);
          if(f!=std::string::npos) {
            find_symbols(expr_lhs, var_set);
            std::set<exprt> var_ls;
            find_symbols(expr_lhs, var_ls);
            cond_vars.insert(var_ls.begin(), var_ls.end());  
          }
          // check if rhs matches any assumption,
          // if so, collect the lhs string
          /*for(exprt::operandst::const_iterator itm=assumption.operands().begin(); 
              itm!=assumption.operands().end(); itm++) {*/
            exprt assume_st = assumption;
            if(expr_rhs==assume_st) {
              assume_lhs.push_back(lhs_str);
              // store variables in assume statement
              // for passing to decision heuristics
              std::set<exprt> symbols_lhs;
              find_symbols(expr_lhs, symbols_lhs);
              assume_vars.insert(symbols_lhs.begin(), symbols_lhs.end());
              acdl_domaint::varst symbols_rhs;
              find_symbols(expr_rhs, symbols_rhs);
              assume_vars.insert(symbols_rhs.begin(), symbols_rhs.end());
              // collect the assumption statements
              assume_statements.push_back(*e_it);
            }
          //}
        }
      }
#ifdef DEBUG
      std::cout << "Original statement: " << from_expr(SSA.ns, "", *e_it) << std::endl;
#endif
    }

    for (local_SSAt::nodet::constraintst::const_iterator c_it=
           n_it->constraints.begin (); c_it!=n_it->constraints.end (); c_it++)
    {
      clist.push_back(*c_it);
#ifdef DEBUG
      std::cout << "Original statement: " << from_expr(SSA.ns, "", *c_it) << std::endl;
#endif
    }

    for (local_SSAt::nodet::assertionst::const_iterator a_it=
           n_it->assertions.begin (); a_it!=n_it->assertions.end (); a_it++)
    {
      clist.push_back(*a_it);
#ifdef DEBUG
      std::cout << "Original statement: " << from_expr(SSA.ns, "", *a_it) << std::endl;
#endif
    }
  }
  
  // Step 1: e=conjunction of all statements;
  exprt e=conjunction(clist);
#ifdef DEBUG
  std::cout << "The conjuncted expression is " << from_expr(SSA.ns, "", e) << std::endl;
#endif

  // Step 2: vars="leaf" variables and variables in assertions
  find_symbols(assertion, var_set);

  for(find_symbols_sett::iterator it=
        var_set.begin(); it!=var_set.end(); ++it)
    var_string.insert(*it);

#ifdef DEBUG
  std::cout << "The final variables are: " << std::endl;
  for(std::set<irep_idt>::iterator it=
        var_string.begin(); it!=var_string.end(); ++it) {
    std::cout << *it << ", " << std::endl;
  }
#endif

#if 0
  // Step 3 [TODO] Turned OFF until fixed
  exprt _s=simplify_transformer(e, var_string, SSA.ns);
  std::cout << "After pre-processing " << std::endl;
  std::cout << from_expr(SSA.ns, "", _s) << std::endl;

  // step 4 [TODO] Turned OFF until the simplify_transformer is fixed
  exprt s=simplify_expr(_s, SSA.ns);
  // std::cout << "The simplified expression is " << from_expr(SSA.ns, "", s) << std::endl;
#endif

  // Step 5
  // worklist.statements=s.operands();
  worklist.statements=e.operands();

// #ifdef DEBUG
  std::cout << "The simplified SSA statements after pre-processing are" << std::endl;
  for(std::vector<exprt>::iterator it=
        worklist.statements.begin(); it!=worklist.statements.end(); it++)
    std::cout << "Statement: " << from_expr(SSA.ns, "", *it) << std::endl;
// #endif
}

/*******************************************************************
 Function: acdl_solvert::operator()

 Inputs:

 Outputs:

 Purpose:
while true do
 S=TOP;
 while true do                                    // PHASE 1: Model Search
  repeat                                          // deduction
    S <- S meet ded(S);
  until S=S meet ded(S);
  if S=bot then break ;                         // conflict
  if complete(ded, S) then return (not BOTTOM, S);  // return SAT model
   S <- decision(S);                              // make decision
 end
 L <- analyse conflict(S) ;                       // PHASE 2: Conflict Analysis
 if L= TOP then return (BOTTOM, L);                // return UNSAT
   ded <- ded meet ded_L;                         // learn: refine transformer
end
\*******************************************************************/

property_checkert::resultt acdl_solvert::operator()(
  const local_SSAt &SSA,
  const exprt &assertion,
  const exprt &additional_constraint,
  const exprt &assumption)
{
  // pre-process SSA
  pre_process(SSA, assertion, assumption);

  // property-driven slicing
  worklist.slicing(SSA, assertion, additional_constraint);

  // collect all symbols for completeness check
  for(std::vector<exprt>::iterator it=worklist.statements.begin(); it!=worklist.statements.end(); it++) {
    acdl_domaint::varst sym;
    find_symbols(*it, sym);
    all_vars.insert(sym.begin(), sym.end());
  }
  std::cout << "The assertion checked now is: " << from_expr(SSA.ns, "", assertion) << std::endl;

#ifdef DEBUG
  std::cout << "Printing all vars" << std::endl;
  for(std::set<symbol_exprt>::iterator it=all_vars.begin();
      it!=all_vars.end();it++) {
    std::cout << from_expr(SSA.ns, "", *it) << std::endl;
  }
  std::cout << "The assertion checked now is: " << from_expr(SSA.ns, "", assertion) << std::endl;
#endif

#ifdef DEBUG
  std::cout << "The assumption is " << from_expr(assumption) << std::endl;
  for(exprt::operandst::const_iterator it=assumption.operands().begin();
      it!=assumption.operands().end(); it++) {
    std::cout << "The assumption operand is " << from_expr(*it) << std::endl;
  }
#endif

  // [TODO] Explicitly make on all assumptions TRUE
  // for example, cond21=(x>0 && X<3), force cond21==TRUE

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
  std::string str4("return_value");
  std::string name;

  for(std::set<exprt>::const_iterator
        it=decision_variable.begin();
      it!=decision_variable.end(); ++it)
  {
    const irep_idt &identifier=it->get(ID_identifier);
    name=id2string(identifier);
    std::size_t found1=name.find(str1);
    std::size_t found2=name.find(str2);
    std::size_t found3=name.find(str3);
    std::size_t found4=name.find(str4);
    if (found1==std::string::npos && found2==std::string::npos &&
        found3==std::string::npos && found4==std::string::npos) {
#if 0
      if(assume_lhs.size()) {
        std::vector<std::string>::iterator its;
        its = find (assume_lhs.begin(), assume_lhs.end(), name);
        if (its == assume_lhs.end()) {
          decision_heuristics.get_dec_variables(*it);
        }
      }
      else {
#endif
       decision_heuristics.get_dec_variables(*it);
      //}
    }
  }

   
  decision_heuristics.initialize_var_set(read_only_vars, assume_vars, cond_vars);
  // [TODO] order decision variables
  decision_heuristics.order_decision_variables(SSA);

#ifdef DEBUG
  std::cout << "Printing all decision variables inside solver" << std::endl;
  for(std::set<exprt>::const_iterator
        it=decision_heuristics.decision_variables.begin();
      it!=decision_heuristics.decision_variables.end(); ++it)
    std::cout << from_expr(SSA.ns, "", *it) << "  , " << std::endl;

  std::cout << "The additional constraint for the loop is: " << from_expr(SSA.ns, "", additional_constraint) << std::endl;
#endif

#if 0
  // collect variables for completeness check
  // all_vars=worklist.live_variables;
#endif

  // initialize values trail
  std::cout << "Compiling" << std::endl;
  init();
  std::cout << "Compiling" << std::endl;

  conflict_graph.init();
  acdl_domaint::valuet v;
  conflict_graph.to_value(v);

  // preprocess abstract value: 
  // transform constraints like 
  // (x==n) to (x<=n) and (x>=n)
  preprocess_val(v);
#ifdef debug
  std::cout << "preprocessed abstract value of implication graph: " << std::endl;
  for(acdl_domaint::valuet::const_iterator it=v.begin();it!=v.end(); ++it)
    std::cout << from_expr(ssa.ns, "", *it) << std::endl;
#endif

  domain.normalize_val(v);
  // check if abstract value v of the
  // implication graph is top for the first time
  // because ACDL starts with TOP
  assert(domain.is_top(v));

  // Note that the optimization below is a risk to apply 
  // since the assumption can be of any shape. And explicitly
  // forcing the assumption on the trail may prevent the domain
  // from deducing other relevant assumptions
  // [OPTIMIZATION] Explicitly store the lhs and rhs 
  // of an assumption in the trail. We do not need to
  // spend time deducing information from the assumption
  // since the assumptions are assumed to be TRUE
  /*for(exprt::operandst::const_iterator it=assumption.operands().begin(); 
      it!=assumption.operands().end(); it++) {*/
    std::cout << "The assumption operand is " << from_expr(assumption) << std::endl;
    exprt assume_st = assumption;
    for(std::vector<exprt>::iterator itw=
        worklist.statements.begin(); itw!=worklist.statements.end(); itw++) 
    {
      exprt stmt = *itw;
      if(itw->id() == ID_equal) {
        exprt rhs=to_equal_expr(stmt).rhs();
        if(rhs==assume_st && assume_st != true_exprt()) { // && assume_st.id() != ID_equal) {  
          exprt lhs=to_equal_expr(stmt).lhs();
          std::vector<acdl_domaint::meet_irreduciblet> ded;
          ded.push_back(lhs);
          conflict_graph.add_deductions(SSA, ded, stmt);
          std::cout << "Pushing deduction from assumption into trail: " << from_expr(lhs) << std::endl;
          ded.clear();
          /*ded.push_back(assume_st);
          conflict_graph.add_deductions(SSA, ded, stmt);
          std::cout << "Pushing deduction from assumption into trail: " << from_expr(assume_st) << std::endl;
          ded.clear();*/
        }
        else {
          continue; 
        }
      }
    }
  //}

  unsigned iteration=0;
  // collect all worklist statements
  // as a conjunction, needed to pass
  // to the gamma-completeness check
  const exprt ssa_conjunction=conjunction(worklist.statements);
  property_checkert::resultt result=property_checkert::UNKNOWN;
  
  // pass ssa_conjunction to the decision heuristics base
  decision_heuristics.initialize_ssa(ssa_conjunction);
  
  // the result is already decided for programs
  // which can be solved only using deductions
  std::cout << "********************************" << std::endl;
  std::cout << "        DEDUCTION PHASE " << std::endl;
  std::cout << "********************************" << std::endl;
  result=propagate(SSA, assertion);
  std::cout << "The result after first propagation phase is " << result << std::endl;
  std::cout << "****************************************************" << std::endl;
  std::cout << " IMPLICATION GRAPH AFTER DEDUCTION PHASE" << std::endl;
  std::cout << "****************************************************" << std::endl;
  conflict_graph.dump_trail(SSA);

  bool complete=false;
  acdl_domaint::valuet res_val;
  acdl_domaint::valuet gamma_decvar;
  // if result=UNSAT, then the proof is complete
  if(result==property_checkert::PASS) {
    std::cout << "The program is SAFE" << std::endl;
    print_solver_statistics();
    return property_checkert::PASS;
  }
  // if result=UNKNOWN or FAIL,
  // then check for completeness
  else {
    // check for satisfying assignment
    conflict_graph.to_value(res_val);
    
    // preprocess abstract value: 
    // transform constraints like 
    // (x==n) to (x<=n) and (x>=n)
    preprocess_val(res_val);
#ifdef debug
    std::cout << "preprocessed abstract value of implication graph: " << std::endl;
    for(acdl_domaint::valuet::const_iterator it=res_val.begin();it!=res_val.end(); ++it)
      std::cout << from_expr(ssa.ns, "", *it) << std::endl;
#endif

    domain.normalize_val(res_val);
    if(domain.is_complete(res_val, all_vars, 
          non_gamma_complete_var, ssa_conjunction, gamma_decvar, read_only_symbols)) {
      complete=true;
      std::cout << "The program in UNSAFE" << std::endl;
      // increase decision count by the
      // decisions made in gamma-complete phase
      decisions+=gamma_decvar.size();
      print_solver_statistics();
      gamma_decvar.clear();
      return property_checkert::FAIL;
    }
  }
  // empty the gamma-complete check_processed
  // statement container and the
  // non_gamma_complete_var container
  gamma_check_processed.clear();
  non_gamma_complete_var.clear();
  gamma_decvar.clear();

  // store the initial values
  // of the decision varaibles
  // after first propagation,
  // needed for largest range heuristics
  initialize_decision_variables(res_val);

  while(true)
  {
    // check the iteration bound
    if(iteration > ITERATION_LIMIT) {
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
    bool status=decide(SSA, assertion);

    if(!status) {
      // if the abstract value is complete and
      // no more decisions can be made, then
      // there is a counterexample. Return result=FAILED.
      if (complete) {
        std::cout << "No further decisions can be made and the program in UNSAFE" << std::endl;
        print_solver_statistics();
        return result;
      }
      std::cout << "Failed to verify program" << std::endl;
#ifdef DEBUG
      acdl_domaint::valuet elm;
      conflict_graph.to_value(elm);

      // preprocess abstract value: 
      // transform constraints like 
      // (x==n) to (x<=n) and (x>=n)
      preprocess_val(elm);
#ifdef debug
      std::cout << "preprocessed abstract value of implication graph: " << std::endl;
      for(acdl_domaint::valuet::const_iterator it=elm.begin();it!=elm.end(); ++it)
        std::cout << from_expr(ssa.ns, "", *it) << std::endl;
#endif

      std::cout << "Minimal unsafe element is" << from_expr(SSA.ns, "", conjunction(elm)) << std::endl;
#endif
      print_solver_statistics();
      return property_checkert::UNKNOWN;
      // break;
    }

    std::cout << "****************************************************" << std::endl;
    std::cout << "IMPLICATION GRAPH AFTER DECISION PHASE" << std::endl;
    std::cout << "****************************************************" << std::endl;
    conflict_graph.dump_trail(SSA);

    std::cout << "********************************" << std::endl;
    std::cout << "        DEDUCTION PHASE " << std::endl;
    std::cout << "********************************" << std::endl;
    result=propagate(SSA, assertion);

    std::cout << "****************************************************" << std::endl;
    std::cout << " IMPLICATION GRAPH AFTER DEDUCTION PHASE" << std::endl;
    std::cout << "****************************************************" << std::endl;
    conflict_graph.dump_trail(SSA);
    // completeness check is done when
    // result=UNKNOWN or result=FAIL
    std::cout << "complete ? " << std::endl;
    if (result==property_checkert::UNKNOWN ||
        result==property_checkert::FAIL)
    {
      // check for satisfying assignment
      acdl_domaint::valuet v;
      conflict_graph.to_value(v); 
      
      // preprocess abstract value: 
      // transform constraints like 
      // (x==n) to (x<=n) and (x>=n)
      preprocess_val(v);
#ifdef debug
      std::cout << "preprocessed abstract value of implication graph: " << std::endl;
      for(acdl_domaint::valuet::const_iterator it=v.begin();it!=v.end(); ++it)
        std::cout << from_expr(ssa.ns, "", *it) << std::endl;
#endif

      // Do we call normalize_val here ? !!
      domain.normalize_val(v);
#ifdef DEBUG
      std::cout << "checking the propagation result UNKNOWN for completeness" << std::endl;
#endif
      // successful execution of is_complete check
      // ensures that all variables are singletons
      // But we invoke another decision phase
      // to infer that "no more decisions can be made"
      if(domain.is_complete(v, all_vars, non_gamma_complete_var, ssa_conjunction, gamma_decvar, read_only_symbols)) {
        // set complete flag to TRUE
        complete=true;
        if(gamma_decvar.size()!=0)
          std::cout << "The program is UNSAFE due to decisions from gamma-complete" << std::endl;
        gamma_check_processed.clear();
        non_gamma_complete_var.clear();
        // increase decision count by the
        // number of decisions made
        // in gamma-complete phase
        decisions+=gamma_decvar.size();
        gamma_decvar.clear();
        print_solver_statistics();
        return property_checkert::FAIL;
      }
      // empty the gamma-complete check_processed
      // statement container and the
      // non_gamma_complete_var container
      gamma_decvar.clear();
      gamma_check_processed.clear();
      non_gamma_complete_var.clear();
    }
    else {
      std::cout << "SUCCESSFULLY PROVEN CASE" << std::endl;
      // empty the gamma-complete check_processed
      // statement container and the
      // non_gamma_complete_var container
      if(gamma_check_processed.size() > 0)
        gamma_check_processed.clear();
      if(non_gamma_complete_var.size() > 0)
        non_gamma_complete_var.clear();
      // check for conflict
      do
      {
        // call generalize_proof here
        // generalize_proof(SSA, assertion, v);

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
            while(i<analyzes_conflict.learned_clauses.size()) {
              acdl_domaint::valuet clause_val=analyzes_conflict.learned_clauses[i];
              const exprt &clause_expr=conjunction(clause_val);
              std::cout << "Learned clause " << i << " is:: " << from_expr(SSA.ns, "", clause_expr) << std::endl;
              i++;
              learned_literals=learned_literals+clause_expr.operands().size();
            }
          }
#endif
          // goto END;
          if (result==property_checkert::PASS) {
            print_solver_statistics();
            return property_checkert::PASS;
          }
          else {
            goto END; // result=UNKNOWN when it breaks for here
          }
        }
        // deduction phase in acdl
        std::cout << "********************************" << std::endl;
        std::cout << "        DEDUCTION PHASE " << std::endl;
        std::cout << "********************************" << std::endl;
        result=propagate(SSA, assertion);
        std::cout << "****************************************************" << std::endl;
        std::cout << " IMPLICATION GRAPH AFTER DEDUCTION PHASE" << std::endl;
        std::cout << "****************************************************" << std::endl;
        conflict_graph.dump_trail(SSA);

      } while(result==property_checkert::PASS); // UNSAT

#if 0
      // [TODO] -- Is this check needed ?
      // check if the result is UNKNOWN
      if (result==property_checkert::UNKNOWN)
      {
        // check for satisfying assignment
        acdl_domaint::valuet v;
        conflict_graph.to_value(v);
        // Do we call normalize_val here ? !!
        domain.normalize_val(v);
#ifdef DEBUG
        std::cout << "checking the propagation result UNKNOWN for completeness" << std::endl;
#endif
        // successful execution of is_complete check
        // ensures that all variables are singletons
        // But we invoke another decision phase
        // to infer that "no more decisions can be made"
        if(domain.is_complete(v, all_vars, non_gamma_complete_var, ssa_conjunction, gamma_decvar, read_only_vars)) {
          // set complete flag to TRUE
          complete=true;
          // empty the gamma-complete check_processed
          // statement container and the
          // non_gamma_complete_var container
          gamma_check_processed.clear();
          non_gamma_complete_var.clear();
          gamma_decvar.clear();
          std::cout << "The program in UNSAFE" << std::endl;
          result=property_checkert::FAIL;
        }
      }
#endif
    }
  } // end of while(true)
END:
  std::cout << "Procedure terminated after iteration: "  << iteration  << std::endl;
  print_solver_statistics();
  return property_checkert::UNKNOWN;
}
