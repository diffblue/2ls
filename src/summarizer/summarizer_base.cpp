/*******************************************************************\

Module: Summarizer Base

Author: Peter Schrammel

\*******************************************************************/

#include <iostream>

#include <util/simplify_expr.h>
#include <solvers/sat/satcheck.h>
#include <solvers/flattening/bv_pointers.h>
#include <solvers/smt2/smt2_dec.h>
#include <util/find_symbols.h>

#include "summarizer_base.h"
#include "summary_db.h"

#include "../domains/ssa_analyzer.h"
#include "../domains/template_generator_summary.h"
#include "../domains/template_generator_callingcontext.h"
#include "../domains/template_generator_ranking.h"

#include "../ssa/local_ssa.h"
#include "../ssa/simplify_ssa.h"

#define PRECISE_JOIN

/*******************************************************************\

Function: summarizer_baset::summarize()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarizer_baset::summarize()
{
  exprt precondition = true_exprt(); //initial calling context
  for(functionst::const_iterator it = ssa_db.functions().begin(); 
      it!=ssa_db.functions().end(); it++)
  {
    status() << "\nSummarizing function " << it->first << eom;
    if(!summary_db.exists(it->first)) 
      compute_summary_rec(it->first,precondition,false);
    else status() << "Summary for function " << it->first << 
           " exists already" << eom;
  }
}

/*******************************************************************\

Function: summarizervt::summarize()

  Inputs:

 Outputs:

 Purpose: summarize from given entry point

\*******************************************************************/

void summarizer_baset::summarize(const function_namet &function_name)
{
  exprt precondition = true_exprt(); //initial calling context

  status() << "\nSummarizing function " << function_name << eom;
  if(!summary_db.exists(function_name)) 
  {
    compute_summary_rec(function_name,precondition,true);
  }
  else status() << "Summary for function " << function_name << 
	 " exists already" << eom;
}

/*******************************************************************\

Function: summarizer_baset::check_call_reachable()

  Inputs:

 Outputs:

 Purpose: returns false if function call is not reachable

\******************************************************************/

bool summarizer_baset::check_call_reachable(
  const function_namet &function_name,
  local_SSAt &SSA,
  local_SSAt::nodest::iterator n_it, 
  local_SSAt::nodet::function_callst::iterator f_it,
  const exprt& precondition,
  bool forward)
{
  assert(f_it->function().id()==ID_symbol); //no function pointers
  irep_idt fname = to_symbol_expr(f_it->function()).get_identifier();

  debug() << "Checking reachability of call to " << fname << eom;

  bool reachable = false;
  // reachability check
  satcheckt satcheck;
  bv_pointerst solver(SSA.ns, satcheck);
  satcheck.set_message_handler(get_message_handler());
  solver.set_message_handler(get_message_handler());
    
  solver << SSA;
  solver << precondition;
  symbol_exprt guard = SSA.guard_symbol(n_it->location);
  ssa_unwinder.get(function_name).unwinder_rename(guard,*n_it,false);
  solver << guard;
  if(!forward) 
    solver << SSA.guard_symbol(--SSA.goto_function.body.instructions.end());

  switch(solver())
  {
  case decision_proceduret::D_SATISFIABLE: {
    reachable = true;
    debug() << "Call is reachable" << eom;
    break; }
  case decision_proceduret::D_UNSATISFIABLE: {
    debug() << "Call is not reachable" << eom;
    break; }
  default: assert(false); break;
  }

  //statistics
  solver_instances++;
  solver_calls++;

  return reachable;
}

/*******************************************************************\

Function: summarizer_baset::compute_calling_context ()

  Inputs:

 Outputs:

 Purpose: computes callee preconditions from the calling context
          for a single function call

\******************************************************************/

exprt summarizer_baset::compute_calling_context(
  const function_namet &function_name, 
  local_SSAt &SSA,
  local_SSAt::nodest::iterator n_it, 
  local_SSAt::nodet::function_callst::iterator f_it,
  const exprt &precondition,
  bool forward)
{
  assert(f_it->function().id()==ID_symbol); //no function pointers
  irep_idt fname = to_symbol_expr(f_it->function()).get_identifier();

  status() << "Computing calling context for function " << fname << eom;

  ssa_analyzert analyzer;
  analyzer.set_message_handler(get_message_handler());

  template_generator_callingcontextt template_generator(
    options,ssa_unwinder.get(function_name));
  template_generator.set_message_handler(get_message_handler());
  template_generator(SSA,n_it,f_it,forward);

  // collect globals at call site
  std::map<local_SSAt::nodet::function_callst::iterator, local_SSAt::var_sett>
    cs_globals_in;
  if(forward) SSA.get_globals(n_it->location,cs_globals_in[f_it]);
  else SSA.get_globals((++n_it)->location,cs_globals_in[f_it]);

  exprt cond = precondition;
  if(!forward) cond = and_exprt(cond,
    SSA.guard_symbol(--SSA.goto_function.body.instructions.end()));

  // analyze
  analyzer(SSA,cond,template_generator);

  // set preconditions
  local_SSAt &fSSA = ssa_db.get(fname); 

  preconditiont precondition_call;
  analyzer.get_result(precondition_call,
		      template_generator.callingcontext_vars());
  ssa_inliner.rename_to_callee(f_it, fSSA.params,
			     cs_globals_in[f_it],fSSA.globals_in,
			     precondition_call);

  debug() << "Calling context for " << 
    from_expr(SSA.ns, "", *f_it) << ": " 
	  << from_expr(SSA.ns, "", precondition_call) << eom;

  //statistics
  solver_instances++;
  solver_calls += analyzer.get_number_of_solver_calls();

  return precondition_call;
}
