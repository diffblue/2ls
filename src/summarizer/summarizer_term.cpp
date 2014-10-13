/*******************************************************************\

Module: Summarizer for Termination Analysis

Author: Peter Schrammel

\*******************************************************************/

#include <iostream>

#include <util/simplify_expr.h>
#include <solvers/sat/satcheck.h>
#include <solvers/flattening/bv_pointers.h>
#include <solvers/smt2/smt2_dec.h>
#include <util/find_symbols.h>

#include "summarizer_term.h"
#include "summary_db.h"

#include "../domains/ssa_analyzer.h"
#include "../domains/template_generator_summary.h"
#include "../domains/template_generator_callingcontext.h"
#include "../domains/template_generator_ranking.h"

#include "../ssa/local_ssa.h"
#include "../ssa/simplify_ssa.h"

/*******************************************************************\

Function: summarizer_baset::summarize()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarizer_termt::summarize()
{
  status() << "\nTermination analysis..."  << eom;
  exprt precondition = true_exprt(); //initial calling context
  for(functionst::const_iterator it = ssa_db.functions().begin(); 
      it!=ssa_db.functions().end(); it++)
  {
    if(summary_db.exists(it->first)) 
      compute_summary_rec(it->first,precondition,false);
    else status() << "Skipping function " << it->first << eom;
  }
}

/*******************************************************************\

Function: summarizert::compute_summary_rec()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarizer_termt::compute_summary_rec(const function_namet &function_name,
				      const exprt &precondition,
				      bool context_sensitive)
{
  assert(!context_sensitive);
  const local_SSAt &SSA = ssa_db.get(function_name); 
  
  status() << "Analyzing function "  << function_name << eom;
  const summaryt &old_summary = summary_db.get(function_name);

  // create summary
  summaryt summary;
  summary.params = SSA.params;
  summary.globals_in = SSA.globals_in;
  summary.globals_out = SSA.globals_out;

  // analyze
  do_termination(function_name, SSA, old_summary, summary);

  // store summary in db
  summary_db.put(function_name,summary);

  {
    std::ostringstream out;
    out << std::endl << "Summary for function " << function_name << std::endl;
    summary_db.get(function_name).output(out,SSA.ns);   
    status() << out.str() << eom;
  }

}

/*******************************************************************\

Function: summarizer_termt::do_termination()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarizer_termt::do_termination(const function_namet &function_name, 
				      const local_SSAt &SSA, 
				      const summaryt &old_summary,
				      summaryt &summary)
{
  status() << "Computing termination argument" << eom;

  // calling context, invariant, function call summaries
  exprt cond = and_exprt(old_summary.fw_invariant,
			 old_summary.fw_precondition);
  cond = and_exprt(cond,
		   ssa_inliner.get_summaries(SSA,true,false));

  if(!check_end_reachable(function_name,SSA,cond))
  {
    summary.terminates = NO;
    return;
  }

  template_generator_rankingt template_generator1(
    options,ssa_unwinder.get(function_name));
  template_generator1.set_message_handler(get_message_handler());
  template_generator1(SSA,true);

  if(template_generator1.all_vars().empty()) return; //nothing to do 

  // compute ranking functions
  ssa_analyzert analyzer1;
  analyzer1.set_message_handler(get_message_handler());
  analyzer1(SSA,cond,template_generator1);
  analyzer1.get_result(summary.termination_argument,template_generator1.all_vars());     

  //extract information whether a ranking function was found for all loops
  summary.terminates = check_termination_argument(summary.termination_argument); 
  //statistics
  solver_instances++;
  solver_calls += analyzer1.get_number_of_solver_calls();
}

/*******************************************************************\

Function: summarizert::check_termination_argument()

  Inputs:

 Outputs:

 Purpose: checks whether a termination argument implies termination

\******************************************************************/

threevalt summarizer_termt::check_termination_argument(exprt expr)
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

Function: summarizer_termt::check_end_reachable()

  Inputs:

 Outputs:

 Purpose: returns false if the end of the function is not reachable

\******************************************************************/

bool summarizer_termt::check_end_reachable(
   const function_namet &function_name,
   const local_SSAt &SSA, 
   const exprt &cond)
{
  satcheckt satcheck;
  bv_pointerst solver(SSA.ns, satcheck);
  satcheck.set_message_handler(get_message_handler());
  solver.set_message_handler(get_message_handler());

  solver << SSA;
  solver << cond;
  solver << SSA.guard_symbol(--SSA.goto_function.body.instructions.end());

  //statistics
  solver_instances++;
  solver_calls++;

  return solver()==decision_proceduret::D_SATISFIABLE;
}
