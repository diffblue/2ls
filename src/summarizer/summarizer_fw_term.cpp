/*******************************************************************\

Module: Summarizer for Forward Analysis

Author: Peter Schrammel

\*******************************************************************/

#include <iostream>

#include <util/simplify_expr.h>
#include <solvers/sat/satcheck.h>
#include <solvers/flattening/bv_pointers.h>
#include <solvers/smt2/smt2_dec.h>
#include <util/find_symbols.h>

#include "summarizer_fw_term.h"
#include "summary_db.h"

#include "../domains/ssa_analyzer.h"
#include "../domains/template_generator_summary.h"
#include "../domains/template_generator_callingcontext.h"
#include "../domains/template_generator_ranking.h"

#include "../ssa/local_ssa.h"
#include "../ssa/simplify_ssa.h"


/*******************************************************************\

Function: summarizert::compute_summary_rec()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarizer_fw_termt::compute_summary_rec(
				      const function_namet &function_name,
				      const exprt &precondition,
				      bool context_sensitive)
{
  local_SSAt &SSA = ssa_db.get(function_name); 
  
  // recursively compute summaries for function calls
  threevalt calls_terminate = YES;
  bool has_function_calls = false;  
  inline_summaries(function_name,SSA,precondition,context_sensitive,
		   calls_terminate,has_function_calls); 

  status() << "Analyzing function "  << function_name << eom;

  {
    std::ostringstream out;
    out << "Function body for " << function_name << 
      " to be analyzed: " << std::endl;
    for(local_SSAt::nodest::iterator n = SSA.nodes.begin(); 
        n!=SSA.nodes.end(); n++)
    {
      if(!n->empty()) n->output(out,SSA.ns);
    }
    out << "(enable) " << from_expr(SSA.ns, "", SSA.get_enabling_exprs()) 
	<< "\n";
    debug() << out.str() << eom;
  }

  bool has_loops = false;  
  if(options.get_bool_option("termination"))
  {
    for(local_SSAt::nodest::iterator n_it = SSA.nodes.begin(); 
        n_it!=SSA.nodes.end(); n_it++)
    {
      if(n_it->loophead != SSA.nodes.end()) { has_loops = true; break; }
    }

    debug() << "function " << 
      (has_function_calls ? "has function calls" : 
       "does not have function calls") << eom;
    debug() << "function calls terminate: " << 
      threeval2string(calls_terminate) << eom;
    debug() << "function " << 
      (has_loops ? "has loops" : "does not have loops") << eom;
  }

  // create summary
  summaryt summary;
  summary.params = SSA.params;
  summary.globals_in = SSA.globals_in;
  summary.globals_out = SSA.globals_out;
  summary.fw_precondition = precondition;

  //compute summary
  if(!options.get_bool_option("havoc"))
  {
    exprt::operandst c;
    if(options.get_bool_option("termination"))
      get_assertions(SSA,c); //assertions as assumptions
    do_summary(function_name,SSA,summary,conjunction(c),context_sensitive);
  }

  //check termination
  if(options.get_bool_option("termination") && 
     !options.get_bool_option("preconditions"))
  {
    status() << "Computing termination argument for " << function_name << eom;
    if(!has_loops && !has_function_calls) 
    {
      status() << "Function trivially terminates" << eom;
      summary.terminates = YES;
    }
    if(!has_loops && has_function_calls && calls_terminate==YES)
    {
      status() << "Function terminates" << eom;
      summary.terminates = YES;
    }   
    if(has_function_calls && calls_terminate!=YES) 
    {
      summary.terminates = UNKNOWN;
      // check non-termination if we haven't analyzed this function yet,
      // otherwise the termination status is UNKNOWN anyways
      if(!summary_db.exists(function_name))
        do_nontermination(function_name,SSA,summary);
    }
    if(has_loops && 
       (!has_function_calls || 
	has_function_calls && calls_terminate==YES))
    {
      do_termination(function_name,SSA,summary);
    }  
  }

  {
    std::ostringstream out;
    out << std::endl << "Summary for function " << function_name << std::endl;
    summary.output(out,SSA.ns);   
    status() << out.str() << eom;
  }

  // store summary in db
  summary_db.put(function_name,summary);
}

/*******************************************************************\

Function: summarizer_fw_termt::inline_summaries()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarizer_fw_termt::inline_summaries(const function_namet &function_name, 
				    local_SSAt &SSA, exprt precondition,
				    bool context_sensitive,
				    threevalt &calls_terminate,
				    bool &has_function_calls)
{
  for(local_SSAt::nodest::iterator n_it = SSA.nodes.begin();
      n_it != SSA.nodes.end(); n_it++)
  {
    for(local_SSAt::nodet::function_callst::iterator f_it = 
	  n_it->function_calls.begin();
        f_it != n_it->function_calls.end(); f_it++)
    {
      assert(f_it->function().id()==ID_symbol); //no function pointers

      if(options.get_bool_option("termination"))
      {
	exprt::operandst c;
	c.push_back(precondition);
	get_assertions(SSA,c); //assertions as assumptions
	precondition = conjunction(c);
      }

      if(!check_call_reachable(function_name,SSA,n_it,f_it,precondition,true)) 
      {
	continue;
      }

      has_function_calls = true;
      irep_idt fname = to_symbol_expr(f_it->function()).get_identifier();

      if(!check_precondition(function_name,SSA,n_it,f_it,
			     precondition,context_sensitive))
      {
	exprt precondition_call = true_exprt();
	if(context_sensitive) 
	  precondition_call = compute_calling_context(
	    function_name,SSA,n_it,f_it,precondition,true);

	status() << "Recursively summarizing function " << fname << eom;
	compute_summary_rec(fname,precondition_call,context_sensitive);
	summaries_used++;
      }

      //get information about callee termination
      if(options.get_bool_option("termination"))
      {
	if(summary_db.exists(fname) && summary_db.get(fname).terminates!=YES) 
	{
	  calls_terminate = UNKNOWN; //cannot propagate NO because call reachability might be over-approximating
	  break;
	}
      }
    }
  }
}

/*******************************************************************\

Function: summarizer_fw_termt::do_nontermination()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarizer_fw_termt::do_nontermination(const function_namet &function_name, 
				      local_SSAt &SSA, 
				      summaryt &summary)
{
  // calling context, invariant, function call summaries
  exprt::operandst cond;
  cond.push_back(summary.fw_invariant);
  cond.push_back(summary.fw_precondition);
  cond.push_back(ssa_inliner.get_summaries(SSA));

  if(!check_end_reachable(function_name,SSA,conjunction(cond)))
  {
    status() << "Function never terminates" << eom;
    if(summary.fw_precondition.is_true()) summary.fw_transformer = false_exprt();
    else summary.fw_transformer = implies_exprt(summary.fw_precondition,false_exprt());
    summary.terminates = NO;
  }
  else
  {
    status() << "Function may terminate" << eom;
  }
}

/*******************************************************************\

Function: summarizer_fw_termt::do_termination()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarizer_fw_termt::do_termination(const function_namet &function_name, 
				      local_SSAt &SSA, 
				      summaryt &summary)
{
  // calling context, invariant, function call summaries
  exprt::operandst cond;
  cond.push_back(summary.fw_invariant);
  cond.push_back(summary.fw_precondition);
  cond.push_back(ssa_inliner.get_summaries(SSA));

  // do non-termination check
  if(!check_end_reachable(function_name,SSA,conjunction(cond)))
  {
    status() << "Function never terminates" << eom;
    if(summary.fw_precondition.is_true()) summary.fw_transformer = false_exprt();
    else summary.fw_transformer = implies_exprt(summary.fw_precondition,false_exprt());
    summary.terminates = NO;
    return;
  }

  status() << "Synthesizing ranking function to prove termination" << eom;
  // solver
  incremental_solvert &solver = ssa_db.get_solver(function_name);
  solver.set_message_handler(get_message_handler());

  template_generator_rankingt template_generator1(
    options,ssa_db,ssa_unwinder.get(function_name));
  template_generator1.set_message_handler(get_message_handler());
  template_generator1(solver.next_domain_number(),SSA,true);

  if(template_generator1.all_vars().empty()) return; //nothing to do 

  get_assertions(SSA,cond); //add assertions as assumptions

  // compute ranking functions
  ssa_analyzert analyzer1;
  analyzer1.set_message_handler(get_message_handler());
  analyzer1(solver,SSA,conjunction(cond),template_generator1);
  analyzer1.get_result(summary.termination_argument,
		       template_generator1.all_vars());     

  //extract information whether a ranking function was found for all loops
  summary.terminates = check_termination_argument(summary.termination_argument); 
  if(!summary.fw_precondition.is_true())
    summary.termination_argument = implies_exprt(summary.fw_precondition,
					       summary.termination_argument);

  //statistics
  solver_instances += analyzer1.get_number_of_solver_instances();
  solver_calls += analyzer1.get_number_of_solver_calls();
}

/*******************************************************************\

Function: summarizer_fw_termt::check_termination_argument()

  Inputs:

 Outputs:

 Purpose: checks whether a termination argument implies termination

\******************************************************************/

threevalt summarizer_fw_termt::check_termination_argument(exprt expr)
{
  if(expr.is_false()) return YES;
  // should be of the form /\_i g_i => R_i
  if(expr.id()==ID_and)
  {
    threevalt result = YES;
    for(exprt::operandst::iterator it = expr.operands().begin(); 
      it != expr.operands().end(); it++)
    {
      if(it->is_true()) result = UNKNOWN;
      if(it->id()==ID_implies)
      {
        if(it->op1().is_true()) result = UNKNOWN;
      }
    }
    return result;
  }
  else
  {
    if(expr.id()==ID_implies)
    {
      if(expr.op1().is_true()) return UNKNOWN;
    }
    else return !expr.is_true() ? YES : UNKNOWN;
  }
  return YES;
}

/*******************************************************************\

Function: summarizer_fw_termt::check_end_reachable()

  Inputs:

 Outputs:

 Purpose: returns false if the end of the function is not reachable

\******************************************************************/

bool summarizer_fw_termt::check_end_reachable(
   const function_namet &function_name,
   local_SSAt &SSA, 
   const exprt &cond)
{
  incremental_solvert &solver = ssa_db.get_solver(function_name);
  solver.set_message_handler(get_message_handler());
  solver << SSA;
  SSA.mark_nodes();

  solver.new_context();
  solver << SSA.get_enabling_exprs();
  solver << ssa_inliner.get_summaries(SSA);

  solver << cond;
  exprt::operandst assertions;
  assertions.push_back(
    SSA.guard_symbol(--SSA.goto_function.body.instructions.end()));
  get_assertions(SSA,assertions);
  solver << disjunction(assertions); //we want to reach any of them

  bool result = (solver()==decision_proceduret::D_SATISFIABLE);

  solver.pop_context();

  return result;
}
