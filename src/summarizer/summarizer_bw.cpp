/*******************************************************************\

Module: Summarizer for Backward Analysis

Author: Peter Schrammel

\*******************************************************************/

#include <iostream>

#include <util/simplify_expr.h>
#include <solvers/sat/satcheck.h>
#include <solvers/flattening/bv_pointers.h>
#include <solvers/smt2/smt2_dec.h>
#include <util/find_symbols.h>

#include "summarizer_bw.h"
#include "summary_db.h"

#include "../domains/ssa_analyzer.h"
#include "../domains/template_generator_summary.h"
#include "../domains/template_generator_callingcontext.h"

#include "../ssa/local_ssa.h"
#include "../ssa/simplify_ssa.h"


/*******************************************************************\

Function: summarizer_bwt::summarize()

  Inputs:

 Outputs:

 Purpose: analyze only functions reachable in a previous forward analysis

\*******************************************************************/

void summarizer_bwt::summarize()
{
  status() << "\nBackward analysis..." << eom;
 
  exprt postcondition = true_exprt(); //initial calling context
  for(functionst::const_iterator it = ssa_db.functions().begin(); 
      it!=ssa_db.functions().end(); it++)
  {
    status() << "\nSummarizing function " << it->first << eom;
    if(summary_db.exists(it->first) &&
       summary_db.get(it->first).bw_precondition.is_nil()) 
      compute_summary_rec(it->first,postcondition,false);
    else status() << "Skipping function " << it->first << eom;
  }
}

/*******************************************************************\

Function: summarizer_bwt::summarize()

  Inputs:

 Outputs:

 Purpose: summarize from given entry point

\*******************************************************************/

void summarizer_bwt::summarize(const function_namet &function_name)
{
  status() << "\nBackward analysis..." << eom;

  exprt postcondition = true_exprt(); //initial calling context

  status() << "\nSummarizing function " << function_name << eom;
  if(summary_db.exists(function_name)) 
  {
    compute_summary_rec(function_name,postcondition,true);
  }
  else status() << "Skipping function " << function_name << eom;
}


/*******************************************************************\

Function: summarizer_bwt::compute_summary_rec()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarizer_bwt::compute_summary_rec(const function_namet &function_name,
				      const exprt &postcondition,
				      bool context_sensitive)
{
  local_SSAt &SSA = ssa_db.get(function_name); 
  
  const summaryt &old_summary = summary_db.get(function_name);

  // recursively compute summaries for function calls
  inline_summaries(function_name,SSA,old_summary,
		   postcondition,context_sensitive,
		   options.get_bool_option("sufficient")); 

  status() << "Analyzing function "  << function_name << eom;

  // create summary
  summaryt summary;
  summary.params = SSA.params;
  summary.globals_in = SSA.globals_in;
  summary.globals_out = SSA.globals_out;
  summary.bw_postcondition = postcondition;

  if(!options.get_bool_option("havoc"))
  {
    do_summary(function_name,SSA,old_summary,summary,context_sensitive);
  }

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

Function: summarizer_bwt::do_summary()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarizer_bwt::do_summary(const function_namet &function_name, 
				local_SSAt &SSA,
				const summaryt &old_summary,
				summaryt &summary,
				bool context_sensitive)
{
  bool sufficient = options.get_bool_option("sufficient");
  status() << "Computing preconditions" << eom;

  // solver
  incremental_solvert &solver = ssa_db.get_solver(function_name);
  solver.set_message_handler(get_message_handler());

  template_generator_summaryt template_generator(
    options,ssa_db,ssa_unwinder.get(function_name));
  template_generator.set_message_handler(get_message_handler());
  template_generator(solver.next_domain_number(),SSA,false);

  exprt::operandst c;
  c.push_back(old_summary.fw_precondition);
  c.push_back(old_summary.fw_invariant);
  c.push_back(ssa_inliner.get_summaries(SSA)); //forward summaries
  exprt::operandst postcond;
  ssa_inliner.get_summaries(SSA,false,postcond,c); //backward summaries
  collect_postconditions(function_name, SSA, summary, postcond,sufficient);
  if(!sufficient)
  {
    c.push_back(conjunction(postcond)); 
  }
  else //sufficient
  {
    c.push_back(not_exprt(conjunction(postcond))); 
  }

  if(!template_generator.out_vars().empty())
  {
    ssa_analyzert analyzer;
    analyzer.set_message_handler(get_message_handler());
    analyzer(solver,SSA,conjunction(c),template_generator);
    analyzer.get_result(summary.bw_transformer,template_generator.inout_vars());
    analyzer.get_result(summary.bw_invariant,template_generator.loop_vars());
    analyzer.get_result(summary.bw_precondition,template_generator.out_vars());

    //statistics
    solver_instances += analyzer.get_number_of_solver_instances();
    solver_calls += analyzer.get_number_of_solver_calls();
  }
  else // TODO: yet another workaround for ssa_analyzer not being able to handle empty templates properly
  {
    solver << SSA;
    solver.new_context();
    solver << SSA.get_enabling_exprs();
    solver << conjunction(c);
    exprt result = true_exprt();
    if(solver()==decision_proceduret::D_UNSATISFIABLE) result = false_exprt();
    solver.pop_context();
    summary.bw_transformer = result;
    summary.bw_invariant = result;
    summary.bw_precondition = result;
  }

  if(sufficient)
  {
    summary.bw_transformer = not_exprt(summary.bw_transformer);
    summary.bw_invariant = not_exprt(summary.bw_invariant);
    summary.bw_precondition = not_exprt(summary.bw_precondition);
  }

  if(context_sensitive && !summary.bw_postcondition.is_true())
  {
    summary.bw_transformer = 
      implies_exprt(summary.bw_postcondition,summary.bw_transformer);
    summary.bw_invariant = 
      implies_exprt(summary.bw_postcondition,summary.bw_invariant);
    summary.bw_precondition = 
      implies_exprt(summary.bw_postcondition,summary.bw_precondition);
  }
}

/*******************************************************************\

Function: summarizer_bwt::inline_summaries()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarizer_bwt::inline_summaries(const function_namet &function_name, 
				   local_SSAt &SSA, 
			           const summaryt &old_summary,
				   const exprt &postcondition,
				   bool context_sensitive,
                                   bool sufficient)
{
  for(local_SSAt::nodest::const_iterator n_it = SSA.nodes.end();
      n_it != SSA.nodes.begin(); )
  {
    n_it--;

    for(local_SSAt::nodet::function_callst::const_iterator f_it = 
	  n_it->function_calls.begin();
        f_it != n_it->function_calls.end(); f_it++)
    {
      assert(f_it->function().id()==ID_symbol); //no function pointers
      if(!sufficient && 
	 !check_call_reachable(function_name,SSA,n_it,f_it,postcondition,false))
      {
	continue;
      }

      if(!check_postcondition(function_name,SSA,n_it,f_it,
			     postcondition,context_sensitive))
      {
	exprt postcondition_call = true_exprt();
	if(context_sensitive) 
	  postcondition_call = compute_calling_context2(
	    function_name,SSA,old_summary,n_it,f_it,postcondition,sufficient);

	irep_idt fname = to_symbol_expr(f_it->function()).get_identifier();
	status() << "Recursively summarizing function " << fname << eom;
	compute_summary_rec(fname,postcondition_call,context_sensitive);
	summaries_used++;
      }
    }
  }
}


/*******************************************************************\

Function: summarizer_bwt::collect_postconditions()

  Inputs:

 Outputs:

 Purpose: collects postconditions where precondition inference starts from

\*******************************************************************/

void summarizer_bwt::collect_postconditions(
  const function_namet &function_name,
  const local_SSAt &SSA, 
  const summaryt &summary,
  exprt::operandst &postconditions,
  bool sufficient)
{
  for(local_SSAt::nodest::const_iterator n_it = SSA.nodes.begin();
      n_it != SSA.nodes.end(); n_it++)
  {
    for(local_SSAt::nodet::assertionst::const_iterator 
	  a_it = n_it->assertions.begin();
	a_it != n_it->assertions.end(); a_it++)
    {
      postconditions.push_back(*a_it);
    }
  }
  /*  if(termination) 
  {
    if(!summary.termination_argument.is_nil()) 
      postconditions.push_back(summary.termination_argument);
      }*/

  exprt guard = SSA.guard_symbol(--SSA.goto_function.body.instructions.end());
  if(!sufficient) 
    postconditions.push_back(and_exprt(guard,summary.bw_postcondition));
  else
    postconditions.push_back(implies_exprt(guard,summary.bw_postcondition));
}

/*******************************************************************\

Function: summarizer_bwt::check_postcondition()

  Inputs:

 Outputs:

 Purpose: returns false if the summary needs to be recomputed

\******************************************************************/

bool summarizer_bwt::check_postcondition(
  const function_namet &function_name,
  const local_SSAt &SSA,
  local_SSAt::nodest::const_iterator n_it, 
  local_SSAt::nodet::function_callst::const_iterator f_it,
  const exprt &precondition,
  bool context_sensitive)
{
  assert(f_it->function().id()==ID_symbol); //no function pointers
  irep_idt fname = to_symbol_expr(f_it->function()).get_identifier();

  status() << "Checking precondition of " << fname << eom;

  bool precondition_holds = false;
  exprt assertion;

  if(!summary_db.exists(fname)) return true; //nothing to do

  summaryt summary = summary_db.get(fname);

  if(summary.bw_precondition.is_nil()) return false; //there is work to do

  if(!context_sensitive ||
     summary.fw_precondition.is_true())  //precondition trivially holds
  {
    status() << "Precondition trivially holds, replacing by summary." 
	     << eom;
    summaries_used++;
    precondition_holds = true;
  }
  else
  {
    assertion = summary.bw_precondition;

    //getting globals at call site
    local_SSAt::var_sett cs_globals_in; 
    SSA.get_globals(n_it->location,cs_globals_in);

    ssa_inliner.rename_to_caller(f_it,summary.params,
				 cs_globals_in,summary.globals_in,assertion);

    debug() << "precondition assertion: " << 
      from_expr(SSA.ns,"",assertion) << eom;

    precondition_holds = false;
  }

  if(precondition_holds) return true;

  assert(!assertion.is_nil());

  // postcondition check
  // solver
  incremental_solvert &solver = ssa_db.get_solver(function_name);
  solver.set_message_handler(get_message_handler());
  solver << SSA;

  solver.new_context();
  solver << SSA.get_enabling_exprs();

  solver << precondition;
  solver << ssa_inliner.get_summaries(SSA);

  //add postcondition
  solver << not_exprt(assertion);

  switch(solver())
  {
  case decision_proceduret::D_SATISFIABLE: {
    precondition_holds = false;

    status() << "Precondition does not hold, need to recompute summary." << eom;
    break; }
  case decision_proceduret::D_UNSATISFIABLE: {
    precondition_holds = true;

    status() << "Precondition holds, replacing by summary." << eom;
    summaries_used++;
                
    break; }
  default: assert(false); break;
  }

  return precondition_holds;
}

/*******************************************************************\

Function: summarizer_bwt::compute_calling_context2()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt summarizer_bwt::compute_calling_context2(  
  const function_namet &function_name, 
  local_SSAt &SSA,
  summaryt old_summary,
  local_SSAt::nodest::const_iterator n_it, 
  local_SSAt::nodet::function_callst::const_iterator f_it,
  const exprt &postcondition,
  bool sufficient)
{
  assert(f_it->function().id()==ID_symbol); //no function pointers
  irep_idt fname = to_symbol_expr(f_it->function()).get_identifier();

  status() << "Computing calling context for function " << fname << eom;

  // solver
  incremental_solvert &solver = ssa_db.get_solver(function_name);
  solver.set_message_handler(get_message_handler());

  //analyze
  ssa_analyzert analyzer;
  analyzer.set_message_handler(get_message_handler());

  template_generator_callingcontextt template_generator(
    options,ssa_db,ssa_unwinder.get(function_name));
  template_generator.set_message_handler(get_message_handler());
  template_generator(solver.next_domain_number(),SSA,n_it,f_it,false);

  // collect globals at call site
  std::map<local_SSAt::nodet::function_callst::const_iterator, local_SSAt::var_sett>
    cs_globals_out;
  SSA.get_globals(n_it->location,cs_globals_out[f_it],false);

  exprt::operandst c;
  c.push_back(old_summary.fw_precondition);
  c.push_back(old_summary.fw_invariant);
  c.push_back(ssa_inliner.get_summaries(SSA)); //forward summaries
  exprt::operandst postcond;
  ssa_inliner.get_summaries(SSA,false,postcond,c); //backward summaries
  old_summary.bw_postcondition = postcondition; //that's a bit awkward
  collect_postconditions(function_name, SSA, old_summary, postcond,sufficient);
  if(!sufficient)
  {
    c.push_back(conjunction(postcond)); 
  }
  else //sufficient
  {
    c.push_back(not_exprt(conjunction(postcond))); 
  }

  analyzer(solver,SSA,conjunction(c),template_generator);

  // set preconditions
  local_SSAt &fSSA = ssa_db.get(fname); 

  exprt postcondition_call;
  analyzer.get_result(postcondition_call,
		      template_generator.callingcontext_vars());

  ssa_inliner.rename_to_callee(f_it, fSSA.params,
			     cs_globals_out[f_it],fSSA.globals_out,
			     postcondition_call);

  if(sufficient && 
     !postcondition_call.is_true()) //TODO: this should actually be handled by ssa_analyzer using a "guard-reachabiliity-only" analysis if template is empty
  {
    postcondition_call = not_exprt(postcondition_call); 
  }

  debug() << "Backward calling context for " << 
    from_expr(SSA.ns, "", *f_it) << ": " 
	  << from_expr(SSA.ns, "", postcondition_call) << eom;

  //statistics
  solver_instances += analyzer.get_number_of_solver_instances();
  solver_calls += analyzer.get_number_of_solver_calls();

  return postcondition_call;
}
 

