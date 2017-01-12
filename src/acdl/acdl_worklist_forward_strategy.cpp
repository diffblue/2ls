/*******************************************************************\

Module: ACDL Worklist Heuristics (Forward Iteration Strategy)

Author: Rajdeep Mukherjee

\*******************************************************************/

#include <algorithm>

#include <util/find_symbols.h>
#include "acdl_worklist_forward_strategy.h"
// #define DEBUG

/*******************************************************************\

  Function: acdl_worklist_orderedt::initialize()

  Inputs:

  Outputs:

  Purpose: 1> Initialize the worklist with all leaf nodes -- for this, we
              collect all non-leaf variables first and then find statements
              which has these non-leaf variables in the rhs
           2> collect all leaf variables for liveness purpose (leaf_vars)
           3> collect all decision variables for decision (worklist_vars)

\*******************************************************************/

void
acdl_worklist_forwardt::initialize(const local_SSAt &SSA,
                                   const exprt &assertion, const exprt& additional_constraint)
{
  // **********************************************************************
  // Initialization Strategy: start with leaf nodes
  // **********************************************************************
  // Iterate over all statements
  // and collect all leaf variables
  // and non-leaf variables
  acdl_domaint::varst sym;
  acdl_domaint::varst temp_leaf_var;
#ifdef DEBUG
  std::cout << "Collecting lhs variables (variables that are assigned)" << std::endl;
#endif
  for(statement_listt::iterator it=statements.begin(); it!=statements.end(); it++) {
    if(it->id()==ID_equal) {
      exprt expr_lhs=to_equal_expr(*it).lhs();
      acdl_domaint::varst lsym;
      find_symbols(expr_lhs, lsym);
      sym.insert(lsym.begin(), lsym.end());
      // populate the worklist_vars at the same time
      // collect all variables in leaf node for
      // preparing decision varaibles in next for loop
      exprt expr_rhs=to_equal_expr(*it).rhs();
      if(expr_rhs.id()==ID_constant || expr_rhs.is_true() || expr_rhs.is_false()) {
        // acdl_domaint::varst rsym;
        // find_symbols(*it, rsym);
        // collect leaf variables
        leaf_vars.insert(lsym.begin(), lsym.end());
      }
    }
    else {
      // don't collect symbols from
      // constraints and assertions
    }
  }

  // populate the worklist
  // with leaf nodes of type Equality only
#ifdef DEBUG
  std::cout << "Searching leaf nodes" << std::endl;
#endif
  for(statement_listt::iterator it=statements.begin(); it!=statements.end(); it++) {
    acdl_domaint::varst sym_rhs;
    acdl_domaint::varst derived_set;
    if(it->id()==ID_equal) {
      exprt expr_rhs=to_equal_expr(*it).rhs();
      find_symbols(expr_rhs, sym_rhs);
      // check if symbols in rhs of a statement
      // exist in non-leaf container "sym"
      // If yes, then this statement is not a leaf node
      set_intersection(sym.begin(), sym.end(), sym_rhs.begin(), sym_rhs.end(),
                       std::inserter(derived_set, derived_set.begin()));
      if(derived_set.empty()) {
#ifdef DEBUG
        std::cout << "Forward Push: " << from_expr(*it) << std::endl;
#endif
        push(*it);
        // collect the leaf variables in the rhs
        // Though these are leaf variables, but we
        // MUST not insert these in to the leaf_vars now
        // since decision variables are computed from leaf_vars next
        // Example: y=x+1, where x=nondet() is a leaf variable
        temp_leaf_var.insert(sym_rhs.begin(), sym_rhs.end());
      }
      // Now prepare the decision variables
      if(expr_rhs.id()==ID_constant || expr_rhs.is_true() || expr_rhs.is_false()) {
        // not inserted into decision variables
      }
      else
      {
        acdl_domaint::varst avars;
        find_symbols(*it, avars);
        // do not insert any leaf variables
        for(acdl_domaint::varst::const_iterator it1=avars.begin(); it1!=avars.end(); ++it1) {
          if(leaf_vars.find(*it1)==leaf_vars.end())
            worklist_vars.insert(*it1);
        }
      }
    }
    // [TODO] special case for ternary statement
    // generated after simplifications
    else {
      acdl_domaint::varst avars;
      find_symbols(*it, avars);
      worklist_vars.insert(avars.begin(), avars.end());
    }
  }
  // Now update the leaf_var
  leaf_vars.insert(temp_leaf_var.begin(), temp_leaf_var.end());

#ifdef DEBUG
  std::cout << "The worklist content after initialisation is: " << std::endl;
  for(std::list<acdl_domaint::statementt>::const_iterator
        it=worklist.begin(); it!=worklist.end(); ++it)
    std::cout << from_expr(SSA.ns, "", *it) << ", ";
  std::cout << std::endl;
#endif
}

/******************************************************************\

Function: acdl_worklist_forwardt::update()

 Inputs:

 Outputs:

 Purpose:

\*****************************************************************/
void acdl_worklist_forwardt::update
( const local_SSAt &SSA,
  const acdl_domaint::varst &vars,
  listt &lexpr,
  const acdl_domaint::statementt &current_statement,
  const exprt& assertion
  )
{
  // dependency analysis loop for
  // equalities, constraints, assertions
  for(statement_listt::iterator e_it=statements.begin(); e_it!=statements.end(); e_it++)
  {
    // the statement has already been processed, so no action needed
    if(*e_it==current_statement) continue;

    if(e_it->id()==ID_equal) {
      exprt expr_rhs=to_equal_expr(*e_it).rhs();
      std::string str("nondet");
      std::string rhs_str=id2string(expr_rhs.get(ID_identifier));
      std::size_t found=rhs_str.find(str);
      // push the nondet statement in rhs
      if(found!=std::string::npos) {
        continue;
      }

      if (check_statement (*e_it, vars)) {
        push_into_list (lexpr, *e_it);
#ifdef DEBUG
        std::cout << "Push: " << from_expr (SSA.ns, "", *e_it) << std::endl;
#endif
      }
    }
#if 0
    // prevents inserting assertion twice
    else if(assertion!=current_statement) {
      if (check_statement (assertion, vars)) {
        push_into_list (lexpr, assertion);
#ifdef DEBUG
        std::cout << "Push: " << from_expr (SSA.ns, "", assertion) << std::endl;
#endif
      }
    }
#endif
    // for constraints and other
    // non-assertion, non-equality statements
    else {
      if (check_statement (*e_it, vars)) {
        push_into_list (lexpr, *e_it);
#ifdef DEBUG
        std::cout << "Push: " << from_expr (SSA.ns, "", *e_it) << std::endl;
#endif
      }
    }
  }
}

#if 0
/*******************************************************************\

Function: acdl_worklist_orderedt::push_into_list()

  Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

void
acdl_worklist_forwardt::push_into_list(listt &lexpr,
                                       const acdl_domaint::statementt &statement)
{
  for(listt::const_iterator it=lexpr.begin();
      it!=lexpr.end(); ++it)
    if(statement==*it)
      return;
  lexpr.push_back(statement);
}
#endif

/*******************************************************************\

  Function: acdl_worklist_orderedt::pop_from_worklist()

  Inputs:

  Outputs:

  Purpose: Variables that are passed to domain is computed as follows:
           1> leaf_rhs_vars=(rhs_vars intersect leaf_vars)
           2> lr_vars=(stmt_vars intersect leaf_rhs_vars)
           3> final_vars=(lhs_vars union lr_vars)
           The condition 2 is a tighter constraint which may lead to
           EMPTY variables, but to obey per-statement based live variable,
           we follow condition 2.

           Alternative approach:
           1> leaf_rhs_vars=(rhs_vars intersect leaf_vars)
           2> final_vars=(lhs_vars union leaf_rhs_vars)

\*******************************************************************/

acdl_domaint::varst acdl_worklist_forwardt::pop_from_map (const acdl_domaint::statementt &statement)
{
  std::map<acdl_domaint::statementt, acdl_domaint::varst>::iterator itf;
  itf=svpair.find(statement);
  acdl_domaint::varst stmt_vars=itf->second;
  // for equalities
  if(itf->first.id()==ID_equal) {
    // find rhs vars
    exprt expr_rhs=to_equal_expr(itf->first).rhs();
    acdl_domaint::varst rhs_vars;
    find_symbols(expr_rhs, rhs_vars);
    // find lhs vars
    exprt expr_lhs=to_equal_expr(itf->first).lhs();
    acdl_domaint::varst lhs_vars;
    find_symbols(expr_lhs, lhs_vars);

    // 1> leaf_rhs_vars=(rhs_vars intersect leaf_vars)
    acdl_domaint::varst leaf_rhs_vars;
    set_intersection(rhs_vars.begin(), rhs_vars.end(), leaf_vars.begin(), leaf_vars.end(),
                     std::inserter(leaf_rhs_vars, leaf_rhs_vars.begin()));

#if 0
    // 2> lr_vars=(stmt_vars intersect intersect leaf_rhs_vars)
    acdl_domaint::varst lr_vars;
    // check if lhs is in map
    set_intersection(stmt_vars.begin(), stmt_vars.end(), leaf_rhs_vars.begin(), leaf_rhs_vars.end(),
                     std::inserter(lr_vars, lr_vars.begin()));
#endif

    // 3> final_vars=(lhs_vars union lr_vars)
    acdl_domaint::varst final_vars;
    final_vars.insert(lhs_vars.begin(), lhs_vars.end());
    // relaxed
    final_vars.insert(leaf_rhs_vars.begin(), leaf_rhs_vars.end());

#if 0
    // constrained
    final_vars.insert(lr_vars.begin(), lr_vars.end());
#endif
    if(final_vars.empty())
    {
      // [TODO] : Do we return empty vars
      return lhs_vars;
    }
    return final_vars;
  }
  // for constraints and assertions
  // pass all the variables in
  // statements to the domain
  else {
    return stmt_vars;
  }
}

/*****************************************************************\

Function: acdl_worklist_baset::update_worklist()

  Inputs:

 Outputs:

 Purpose:

\******************************************************************/
void acdl_worklist_forwardt::update
( const local_SSAt &SSA,
  const acdl_domaint::varst &vars,
  const acdl_domaint::statementt &current_statement,
  const exprt& assertion
  )
{
  live_variables.insert(vars.begin(), vars.end());
  // [NORMAL CASE] Delete map element since
  // corresponding worklist element is also deleted.
  delete_from_map(current_statement);
  // dependency analysis loop for
  // equalities, constraints, assertions
  for(statement_listt::iterator e_it=statements.begin(); e_it!=statements.end(); e_it++)
  {
    // the statement has already been
    // processed, so no action needed
    if(*e_it==current_statement) continue;

    // push into map
    push_into_map(*e_it, vars);
    acdl_domaint::varst c_vars;
    find_symbols(*e_it, c_vars);
    // this is maintained for old live varaible approach
    live_variables.insert(c_vars.begin(), c_vars.end());

    if(e_it->id()==ID_equal) {
      exprt expr_rhs=to_equal_expr(*e_it).rhs();
      // check only the rhs
      if(check_statement(expr_rhs, vars))
        push(*e_it);
    }
    // for constraints and other
    // non-equality statements,
    // check intersection of all symbols
    else {
      if (check_statement (*e_it, vars))
        push(*e_it);
    }
  }
  // remove variables of popped statement from live variables
  remove_live_variables(SSA, current_statement);
#ifdef DEBUG
  std::cout << "The content of the updated worklist is as follows: " << std::endl;
  for(std::list<acdl_domaint::statementt>::const_iterator
        it=worklist.begin(); it!=worklist.end(); ++it) {
    std::cout << "Updated Worklist Element::" << from_expr(SSA.ns, "", *it) << "===>";
    std::map<acdl_domaint::statementt, acdl_domaint::varst>::iterator itf;
    itf=svpair.find(*it);
    acdl_domaint::varst lvar=itf->second;
    for(acdl_domaint::varst::const_iterator it1=
          lvar.begin(); it1!=lvar.end(); ++it1)
      std::cout << from_expr(*it1) << ", ";
    std::cout << std::endl;
  }
#endif
}

/************************************************************\

  Function: acdl_worklist_forwardt::dec_update()

  Inputs:

  Outputs:

  Purpose: Initialize the worklist after a decision is made

\*******************************************************************/

void acdl_worklist_forwardt::dec_update(const local_SSAt &SSA,
                                        const acdl_domaint::meet_irreduciblet &expr, const exprt& assertion)
{
  acdl_domaint::varst new_live_variables;
  acdl_domaint::varst vars;
  find_symbols(expr, vars);

  // dependency analysis loop for
  // equalities, constraints, assertions
  for(statement_listt::iterator e_it=statements.begin();
      e_it!=statements.end(); e_it++)
  {
    acdl_domaint::varst c_vars;
    find_symbols(*e_it, c_vars);
    if(e_it->id()==ID_equal) {
      exprt expr_rhs=to_equal_expr(*e_it).rhs();
      // check only the rhs
      if(check_statement(expr_rhs, vars)) {
        push(*e_it);
        new_live_variables.insert(c_vars.begin(), c_vars.end());
      }
      // special case for left
      // to right deductions in forward strategy
      // example: cond21=(x==y), decision is made
      // on cond21, so we need to also insert this statement
      // since this would allow the deduction (x==y)
      exprt expr_lhs=to_equal_expr(*e_it).lhs();
      // check only the lhs
      if(check_statement(expr_lhs, vars)) {
        push(*e_it);
        new_live_variables.insert(c_vars.begin(), c_vars.end());
      }
    }
    // for constraints and other
    // non-equality statements,
    // check intersection of all symbols
    else {
      if (check_statement (*e_it, vars)) {
        push(*e_it);
        new_live_variables.insert(c_vars.begin(), c_vars.end());
      }
    }
  }

  // now create the live variable list per statement
  // Note that the worklist is always empty before
  // calling dec_update, so we need to initialize the
  // live variable again per statement wise.
  initialize_live_variables();
}
