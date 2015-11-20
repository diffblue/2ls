/*******************************************************************\

Module: ACDL Solver

Author: Rajdeep Mukherjee, Peter Schrammel

\*******************************************************************/


#include <langapi/language_util.h>
#include <util/find_symbols.h>
#include "acdl_solver.h"
#include "acdl_domain.h"

#define DEBUG


#ifdef DEBUG
#include <iostream>
#endif

/*******************************************************************\

Function: acdl_solvert::operator()

  Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/


void
acdl_solvert::initialize_worklist (const local_SSAt &SSA, worklistt &worklist)
{
  // check for equalitites or constraints or next node
  if (SSA.nodes.empty ())
    return;
  assert(!SSA.nodes.front ().equalities.empty ());
  // insert the first element on to the worklist
  push_into_worklist(worklist, SSA.nodes.front ().equalities.front ());
  #ifdef DEBUG
  std::cout << "First push: " << from_expr (SSA.ns, "", SSA.nodes.front().equalities.front ()) << std::endl;
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
    for (local_SSAt::nodet::constraintst::const_iterator e_it =
        n_it->constraints.begin (); e_it != n_it->constraints.end (); e_it++)
    {
      if(*e_it == current_statement) continue;
      if (check_statement (*e_it, vars)) {
        push_into_worklist(worklist, *e_it);
        #ifdef DEBUG
        std::cout << "Push: " << from_expr (SSA.ns, "", *e_it) << std::endl;
        #endif
      }
    }
    for (local_SSAt::nodet::assertionst::const_iterator e_it =
        n_it->assertions.begin (); e_it != n_it->assertions.end (); e_it++)
    {
      if(*e_it == current_statement) continue;
      if (check_statement (*e_it, vars)) {
        push_into_worklist(worklist, not_exprt (*e_it));
        #ifdef DEBUG
        std::cout << "Push: " << from_expr (SSA.ns, "", not_exprt(*e_it)) << std::endl;
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
  // If it is an equality, then select the lhs for post-condition computation
  exprt lhs;
  if (statement.id () == ID_equal)
  {
    lhs = to_equal_expr (statement).lhs ();
    if (lhs.id () == ID_symbol)
    {
      vars.push_back (to_symbol_expr (lhs));
    }
    else //TODO: more complex lhs
      assert(false);
  }
  else // for constraints
  {
    std::set<symbol_exprt> symbols;
    find_symbols(statement,symbols);
    vars.insert(vars.end(),symbols.begin(), symbols.end());
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

property_checkert::resultt acdl_solvert::propagate(const local_SSAt &SSA, acdl_domaint::valuet &v)
{
#if 0
  unsigned iteration_number=0;
  bool change;
#endif
  
  worklistt worklist;
  
  initialize_worklist(SSA, worklist);

#if 1
  exprt expression;
  std::list<acdl_domaint::statementt> equalities_expr;
   std::list<acdl_domaint::statementt> constraints_expr;
   std::list<acdl_domaint::statementt> assertions_expr;
  // collect all equalities, constraints and assertions
  for(local_SSAt::nodest::const_iterator n_it = SSA.nodes.begin();
      n_it != SSA.nodes.end(); n_it++) {
    for(local_SSAt::nodet::equalitiest::const_iterator e_it =
	 	  n_it->equalities.begin(); e_it != n_it->equalities.end(); e_it++) {
       expression = *e_it;
       assert(e_it->id()==ID_equal);
       //std::cout<< "The expression is " << e_it->pretty() << std::endl;
       equalities_expr.push_back(expression);
    }
    for(local_SSAt::nodet::assertionst::const_iterator a_it =
    	  n_it->assertions.begin(); a_it != n_it->assertions.end(); a_it++) {
         expression = *a_it;
         assertions_expr.push_back(expression);
    }
    
    for(local_SSAt::nodet::constraintst::const_iterator c_it =
    	  n_it->constraints.begin(); c_it != n_it->constraints.end(); c_it++) {
         expression = *c_it;
         constraints_expr.push_back(expression);
    }
  }
#endif
  while (!worklist.empty())
  {
    const acdl_domaint::statementt statement = pop_from_worklist(worklist);
    
    #ifdef DEBUG
    std::cout << "Pop: " << from_expr (SSA.ns, "", statement)
        << std::endl;
    #endif
    acdl_domaint::varst vars;
    std::vector<acdl_domaint::valuet> new_v;
    new_v.resize (1);
    // TODO: this is a workaround to handle booleans,
    //       must be implemented using a product domain
    if (statement.id () == ID_equal
        && to_equal_expr (statement).lhs ().type ().id () == ID_bool)
    {
      new_v[0] = statement;
      // collect variables for dependencies
      std::set<symbol_exprt> symbols;
      find_symbols(statement,symbols);
      vars.insert(vars.end(),symbols.begin(), symbols.end());
    }
    else
    {
      // select vars according to iteration strategy
      select_vars (statement, vars);
#ifdef DEBUG
      std::cout << "Selected vars:";
      for(acdl_domaint::varst::const_iterator v_it = vars.begin();
	  v_it != vars.end(); ++v_it)
	std::cout << " " << from_expr (SSA.ns, "", *v_it);
      std::cout << std::endl;
#endif

      // compute update of abstract value
      domain (statement, vars, v, new_v[0]);
    }
    // terminating condition check for populating worklist
    if(!domain.contains(v, new_v[0]))
    {
      update_worklist(SSA, vars, worklist, statement);
    }

#ifdef DEBUG
    std::cout << "Old: " << from_expr (SSA.ns, "", v)
              << std::endl;
    std::cout << "New: " << from_expr (SSA.ns, "", new_v[0])
              << std::endl;
#endif

    // meet is computed because we are doing gfp
    domain.meet (new_v, v);
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
  acdl_domaint::valuet v;
  domain.set_top(v);
  property_checkert::resultt result = property_checkert::UNKNOWN;

  while(true)
  {
    while(true)
    {
      // deduction phase in acdl
      result = propagate(SSA, v);

      // check for conflict
      if(result == property_checkert::PASS) //UNSAT
        break;
    
      // check for satisfying assignment
      if(domain.is_complete(v))
        return property_checkert::FAIL;

      //TODO: to make it terminate for now:
      return result;
    }

    // analyze conflict ...


    //TODO: to make it terminate for now:
    return result;
  }
}
