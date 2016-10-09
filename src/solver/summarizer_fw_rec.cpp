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

#include "summarizer_fw_rec.h"
#include "summary_db.h"

#include <domains/ssa_analyzer.h>
#include <domains/template_generator_recsum.h>

#include <ssa/local_ssa.h>

//#define SHOW_WHOLE_RESULT

/*******************************************************************\

Function: summarizer_fw_rect::summarize()

  Inputs:

 Outputs:

 Purpose: summarize from given entry point

\*******************************************************************/

void summarizer_fw_rect::summarize(const function_namet &function_name)
{
  //initialise summaries
  for(functionst::const_iterator it = ssa_db.functions().begin(); 
      it!=ssa_db.functions().end(); it++)
  {
    const local_SSAt &SSA = ssa_db.get(it->first);
    summaryt summary;
    summary.params = SSA.params;
    summary.globals_in = SSA.globals_in;
    summary.globals_out = SSA.globals_out;
    summary.fw_precondition = true_exprt();
    if(it->first==function_name)
      summary.fw_transformer=true_exprt();
    else
      summary.fw_transformer=false_exprt();
    summary.fw_invariant = true_exprt();
    summary.mark_recompute=true;
    summary_db.put(it->first,summary);
  }

  exprt precondition = true_exprt(); //initial calling context

  status() << "\nSummarizing function " << function_name << eom;
  if(!summary_db.exists(function_name) || 
     summary_db.get(function_name).mark_recompute) 
  {
    compute_summary_rec(function_name,precondition,
                        options.get_bool_option("context-sensitive"));
  }
  else status() << "Summary for function " << function_name << 
	 " exists already" << eom;
}

/*******************************************************************\

Function: summarizer_fw_rect::compute_summary_rec()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarizer_fw_rect::compute_summary_rec(
  const function_namet &function_name,
  const exprt &precondition,
  bool context_sensitive)
{
  local_SSAt &SSA = ssa_db.get(function_name); //TODO: make const
  bool changed=false;
  do //compute lfp
  {
    // recursively compute summaries for function calls
    inline_summaries(function_name,SSA,precondition,context_sensitive); 

    status() << "Analyzing function "  << function_name << eom;

    // create summary
    summaryt summary;
    summary.params = SSA.params;
    summary.globals_in = SSA.globals_in;
    summary.globals_out = SSA.globals_out;
    summary.fw_precondition = precondition;
    summary.fw_invariant = true_exprt();

    do_summary(function_name,SSA,summary,true_exprt(),context_sensitive);

    // store summary in db
    summaryt old_summary=summary_db.get(function_name);
    summary_db.put(function_name,summary);
    changed=!is_contained(summary.fw_transformer,old_summary.fw_transformer,SSA.ns);

    if(!options.get_bool_option("competition-mode"))
    {
      std::ostringstream out;
      out << std::endl << "Summary for function " << function_name << std::endl;
      summary_db.get(function_name).output(out,SSA.ns);   
      status() << out.str() << eom;
    }
  }
  while(changed);
}

/*******************************************************************\

Function: summarizer_fw_rect::do_summary()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarizer_fw_rect::do_summary(const function_namet &function_name, 
                                    local_SSAt &SSA,
                                    summaryt &summary,
                                    exprt cond,
                                    bool context_sensitive)
{
  status() << "Computing summary" << eom;

  // solver
  incremental_solvert &solver = ssa_db.get_solver(function_name);
  solver.set_message_handler(get_message_handler());

  //analyze
  ssa_analyzert analyzer;
  analyzer.set_message_handler(get_message_handler());

  template_generator_recsumt template_generator(
    options,ssa_db,ssa_unwinder.get(function_name));
  template_generator.set_message_handler(get_message_handler());
  template_generator(solver.next_domain_number(),SSA,true);

  exprt::operandst conds;
  conds.reserve(5);
  conds.push_back(cond);
  conds.push_back(summary.fw_precondition);
  conds.push_back(ssa_inliner.get_summaries(SSA));

  cond = conjunction(conds);

  analyzer(solver,SSA,cond,template_generator);
  analyzer.get_result(summary.fw_transformer,template_generator.inout_vars());

  if(context_sensitive && !summary.fw_precondition.is_true())
  {
    summary.fw_transformer = 
      implies_exprt(summary.fw_precondition,summary.fw_transformer);
  }

  solver_instances += analyzer.get_number_of_solver_instances();
  solver_calls += analyzer.get_number_of_solver_calls();
}

/*******************************************************************\

Function: summarizer_fw_rect::inline_summaries()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarizer_fw_rect::inline_summaries(
  const function_namet &function_name, 
  local_SSAt &SSA, const exprt &precondition,
  bool context_sensitive)
{
  for(local_SSAt::nodest::const_iterator n_it = SSA.nodes.begin();
      n_it != SSA.nodes.end(); n_it++)
  {
    for(local_SSAt::nodet::function_callst::const_iterator f_it = 
          n_it->function_calls.begin();
        f_it != n_it->function_calls.end(); f_it++)
    {
      irep_idt fname = to_symbol_expr(f_it->function()).get_identifier();
      if(fname==function_name) //we do recursive calls later
        continue;
/*
      if(!check_call_reachable(function_name,SSA,n_it,f_it,precondition,true)) 
        continue;

      if(!check_precondition(function_name,SSA,n_it,f_it,
                             precondition,context_sensitive))
                             {*/
        exprt precondition_call = true_exprt();
        if(context_sensitive) 
          precondition_call = compute_calling_context(
            function_name,SSA,n_it,f_it,precondition,true);

        status() << "Recursively summarizing function " << fname << eom;
        compute_summary_rec(fname,precondition_call,context_sensitive);
        summaries_used++;
//      }
    }
  }
}


