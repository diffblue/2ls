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

#include "summarizer_fw.h"
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

void summarizer_fwt::compute_summary_rec(const function_namet &function_name,
				      const exprt &precondition,
				      bool context_sensitive)
{
  local_SSAt &SSA = ssa_db.get(function_name); //TODO: make const
  
  // recursively compute summaries for function calls
  inline_summaries(function_name,SSA,precondition,context_sensitive); 

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

  // create summary
  summaryt summary;
  summary.params = SSA.params;
  summary.globals_in = SSA.globals_in;
  summary.globals_out = SSA.globals_out;
  summary.fw_precondition = precondition;

  if(!options.get_bool_option("havoc"))
  {
    do_summary(function_name,SSA,summary,context_sensitive);
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

Function: summarizer_fwt::do_summary()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarizer_fwt::do_summary(const function_namet &function_name, 
				local_SSAt &SSA,
				summaryt &summary,
				bool context_sensitive)
{
  status() << "Computing summary" << eom;

  //analyze
  ssa_analyzert analyzer;
  analyzer.set_message_handler(get_message_handler());

  template_generator_summaryt template_generator(
    options,ssa_unwinder.get(function_name));
  template_generator.set_message_handler(get_message_handler());
  template_generator(SSA,true);

  exprt cond = and_exprt(summary.fw_precondition,
			 ssa_inliner.get_summaries(SSA,true,false));

  analyzer(SSA,cond,template_generator);
  analyzer.get_result(summary.fw_transformer,template_generator.inout_vars());
  analyzer.get_result(summary.fw_invariant,template_generator.loop_vars());

  if(context_sensitive && !summary.fw_precondition.is_true())
  {
    summary.fw_transformer = 
      implies_exprt(summary.fw_precondition,summary.fw_transformer);
    summary.fw_invariant = 
      implies_exprt(summary.fw_precondition,summary.fw_invariant);
  }

  //statistics
  solver_instances++;
  solver_calls += analyzer.get_number_of_solver_calls();
}

/*******************************************************************\

Function: summarizer_fwt::inline_summaries()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarizer_fwt::inline_summaries(const function_namet &function_name, 
				   local_SSAt &SSA, const exprt &precondition,
				   bool context_sensitive)
{
  for(local_SSAt::nodest::iterator n_it = SSA.nodes.begin();
      n_it != SSA.nodes.end(); n_it++)
  {
    for(local_SSAt::nodet::function_callst::iterator f_it = 
	  n_it->function_calls.begin();
        f_it != n_it->function_calls.end(); f_it++)
    {
      assert(f_it->function().id()==ID_symbol); //no function pointers
      if(!check_call_reachable(function_name,SSA,n_it,f_it,precondition,true)) 
      {
	continue;
      }

      if(!check_precondition(function_name,SSA,n_it,f_it,
			     precondition,context_sensitive))
      {
	exprt precondition_call = true_exprt();
	if(context_sensitive) 
	  precondition_call = compute_calling_context(
	    function_name,SSA,n_it,f_it,precondition,true);

	irep_idt fname = to_symbol_expr(f_it->function()).get_identifier();
	status() << "Recursively summarizing function " << fname << eom;
	compute_summary_rec(fname,precondition_call,context_sensitive);
	summaries_used++;
      }
    }
  }
}

/*******************************************************************\

Function: summarizer_fwt::check_precondition()

  Inputs:

 Outputs:

 Purpose: returns false if the summary needs to be recomputed

\******************************************************************/

bool summarizer_fwt::check_precondition(
  const function_namet &function_name,
  local_SSAt &SSA,
  local_SSAt::nodest::iterator n_it, 
  local_SSAt::nodet::function_callst::iterator f_it,
  const exprt &precondition,
  bool context_sensitive)
{
  assert(f_it->function().id()==ID_symbol); //no function pointers
  irep_idt fname = to_symbol_expr(f_it->function()).get_identifier();

  status() << "Checking precondition of " << fname << eom;

  bool precondition_holds = false;

  if(summary_db.exists(fname)) 
  {
    summaryt summary = summary_db.get(fname);
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
      exprt assertion = summary.fw_precondition;

      //getting globals at call site
      local_SSAt::var_sett cs_globals_in; 
      SSA.get_globals(n_it->location,cs_globals_in);

      ssa_inliner.rename_to_caller(f_it,summary.params,
			       cs_globals_in,summary.globals_in,assertion);

      n_it->assertions.push_back(assertion);
      debug() << "precondition assertion: " << 
	from_expr(SSA.ns,"",assertion) << eom;

      precondition_holds = false;
    }
  }
  else if(!ssa_db.exists(fname))
  {
    status() << "Function " << fname << " not found" << eom;
    precondition_holds = true;
  }
  else if(fname == function_name) 
  {
    status() << "Havoc recursive function call to " << fname << eom;
    precondition_holds = true;
  }
  else 
  {
    status() << "Function " << fname << " not analyzed yet" << eom;
    return false; //function not seen yet
  }

  if(precondition_holds) return true;

  // precondition check
  satcheckt satcheck;
  bv_pointerst solver(SSA.ns, satcheck);
  satcheck.set_message_handler(get_message_handler());
  solver.set_message_handler(get_message_handler());
    
  solver << precondition;
  solver << SSA;
  solver << not_exprt(n_it->assertions.front());

  switch(solver())
  {
  case decision_proceduret::D_SATISFIABLE: {
    precondition_holds = false;
    n_it->assertions.clear();

    status() << "Precondition does not hold, need to recompute summary." << eom;
    break; }
  case decision_proceduret::D_UNSATISFIABLE: {
    precondition_holds = true;
    n_it->assertions.clear();

    status() << "Precondition holds, replacing by summary." << eom;
    summaries_used++;
                
    break; }
  default: assert(false); break;
  }

  //statistics
  solver_instances++;
  solver_calls++;

  return precondition_holds;
}

