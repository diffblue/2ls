/*******************************************************************\

Module: Summarizer for Forward Analysis

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Summarizer for Forward Analysis

#include <iostream>

#include <util/simplify_expr.h>
#include <solvers/sat/satcheck.h>
#include <solvers/flattening/bv_pointers.h>
#include <solvers/smt2/smt2_dec.h>
#include <util/find_symbols.h>

#include "summarizer_fw.h"

#include <domains/ssa_analyzer.h>
#include <domains/template_generator_summary.h>

// #define SHOW_WHOLE_RESULT

void summarizer_fwt::compute_summary_rec(
  const function_namet &function_name,
  const exprt &precondition,
  bool context_sensitive)
{
  local_SSAt &SSA=ssa_db.get(function_name); // TODO: make const

  // recursively compute summaries for function calls
  inline_summaries(function_name, SSA, precondition, context_sensitive);

  status() << "Analyzing function "  << function_name << eom;

#if 0
  {
    std::ostringstream out;
    out << "Function body for " << function_name
        << " to be analyzed: " << std::endl;
    for(const auto &node : SSA.nodes)
    {
      if(!node.empty())
        node.output(out, SSA.ns);
    }
    out << "(enable) " << from_expr(SSA.ns, "", SSA.get_enabling_exprs())
        << "\n";
    debug() << out.str() << eom;
  }
#endif

  // create summary
  summaryt summary;
  summary.params=SSA.params;
  summary.globals_in=SSA.globals_in;
  summary.globals_out=SSA.globals_out;
  summary.set_value_domains(SSA);
  summary.fw_precondition=precondition;

  if(!options.get_bool_option("havoc"))
  {
    do_summary(function_name, SSA, summary, true_exprt(), context_sensitive);
  }


#if 0
  if(!options.get_bool_option("competition-mode"))
  {
    std::ostringstream out;
    out << std::endl << "Summary for function " << function_name << std::endl;
    summary.output(out, SSA.ns);
    status() << out.str() << eom;
  }
#endif

  // store summary in db
  summary_db.put(function_name, summary);

  if(!options.get_bool_option("competition-mode"))
  {
    std::ostringstream out;
    out << std::endl << "Summary for function " << function_name << std::endl;
    summary_db.get(function_name).output(out, SSA.ns);
    status() << out.str() << eom;
  }
}

void summarizer_fwt::do_summary(
  const function_namet &function_name,
  local_SSAt &SSA,
  summaryt &summary,
  exprt cond,
  bool context_sensitive)
{
  status() << "Computing summary" << eom;

  // solver
  incremental_solvert &solver=ssa_db.get_solver(function_name);
  solver.set_message_handler(get_message_handler());

  // analyze
  ssa_analyzert analyzer;
  analyzer.set_message_handler(get_message_handler());

  template_generator_summaryt template_generator(
    options, ssa_db, ssa_unwinder.get(function_name));
  template_generator.set_message_handler(get_message_handler());
  template_generator(solver.next_domain_number(), SSA, true);

  exprt::operandst conds;
  conds.reserve(5);
  conds.push_back(cond);
  conds.push_back(summary.fw_precondition);
  conds.push_back(ssa_inliner.get_summaries(SSA));

#ifdef REUSE_INVARIANTS
  if(summary_db.exists(function_name)) // reuse existing invariants
  {
    const exprt &old_inv=summary_db.get(function_name).fw_invariant;
    exprt inv=ssa_unwinder.get(function_name).rename_invariant(old_inv);
    conds.push_back(inv);

#if 0
    std::ostringstream out;
    out << "(original inv)" << from_expr(SSA.ns, "", old_inv) << "\n";
    debug() << out.str() << eom;
    out << "(renamed inv)" << from_expr(SSA.ns, "", inv) << "\n";
    debug() << out.str() << eom;
#endif
  }
#endif

  cond=conjunction(conds);

  analyzer(solver, SSA, cond, template_generator);
  analyzer.get_result(summary.fw_transformer, template_generator.inout_vars());
  analyzer.get_result(summary.fw_invariant, template_generator.loop_vars());

#ifdef SHOW_WHOLE_RESULT
  // to see all the custom template values
  exprt whole_result;
  analyzer.get_result(whole_result, template_generator.all_vars());
  debug() << "whole result: " << from_expr(SSA.ns, "", whole_result) << eom;
#endif

  if(options.get_bool_option("heap"))
  {
    analyzer.update_heap_out(summary.globals_out);
    const exprt advancer_bindings=analyzer.input_heap_bindings();
    if(!advancer_bindings.is_true())
    {
      summary.aux_precondition=advancer_bindings;
    }
  }

  if(context_sensitive && !summary.fw_precondition.is_true())
  {
    summary.fw_transformer=
      implies_exprt(summary.fw_precondition, summary.fw_transformer);
    summary.fw_invariant=
      implies_exprt(summary.fw_precondition, summary.fw_invariant);
  }

  solver_instances+=analyzer.get_number_of_solver_instances();
  solver_calls+=analyzer.get_number_of_solver_calls();
}

void summarizer_fwt::inline_summaries(
  const function_namet &function_name,
  local_SSAt &SSA, const exprt &precondition,
  bool context_sensitive)
{
  for(local_SSAt::nodest::const_iterator n_it=SSA.nodes.begin();
      n_it!=SSA.nodes.end(); n_it++)
  {
    for(local_SSAt::nodet::function_callst::const_iterator f_it=
          n_it->function_calls.begin();
        f_it!=n_it->function_calls.end(); f_it++)
    {
      assert(f_it->function().id()==ID_symbol); // no function pointers
      if(!check_call_reachable(
           function_name, SSA, n_it, f_it, precondition, true))
      {
        continue;
      }

      if(!check_precondition(
           function_name, SSA, n_it, f_it, precondition, context_sensitive))
      {
        exprt precondition_call=true_exprt();
        if(context_sensitive)
          precondition_call=compute_calling_context(
            function_name, SSA, n_it, f_it, precondition, true);

        irep_idt fname=to_symbol_expr(f_it->function()).get_identifier();
        status() << "Recursively summarizing function " << fname << eom;
        compute_summary_rec(fname, precondition_call, context_sensitive);
        summaries_used++;
      }
    }
  }
}


