/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/* 
 * File:   summarizer_rec_fwt.cpp
 * Author: sarbojit
 * 
 * Created on 13 March, 2018, 4:53 PM
 */

#include <domains/ssa_analyzer.h>
#include <domains/template_gen_rec_summary.h>
#include <algorithm>
#include "summarizer_rec_fw.h"

void summarizer_rec_fwt::compute_summary_rec(
  const function_namet &function_name,
  const exprt &precondition,
  bool context_sensitive)
{
  local_SSAt &SSA=ssa_db.get(function_name);// TODO: make const
    
  bool recursive=false;
  for(local_SSAt::nodet node:SSA.nodes)
  {
    for(function_application_exprt f_call:node.function_calls)
      if(function_name==to_symbol_expr(f_call.function()).get_identifier() &&
         f_call.function().id()==ID_symbol)//No function pointer
        recursive=true;
  }
  if(recursive)//if this_function_is_recursive
  {
    status()<<"Function "<<function_name.c_str()<<" is recursive"<<eom;
    //inline other non-recursive functions in the same SCC of the call graph
    //this makes it self recursive
  }
    
  // recursively compute summaries for non-recursive function calls
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
  //if(recursive) summary.fw_precondition=true;
  summary.fw_precondition=precondition;
  
  if(!options.get_bool_option("havoc"))
  {
    do_summary(function_name, SSA, summary,
               true_exprt(),context_sensitive, recursive);
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

void summarizer_rec_fwt::do_summary(
  const function_namet &function_name,
  local_SSAt &SSA,
  summaryt &summary,
  exprt cond,
  bool context_sensitive,
  bool recursive)
{
  status() << "Computing summary" << eom;
  
  // solver
  incremental_solvert &solver=ssa_db.get_solver(function_name);
  solver.set_message_handler(get_message_handler());
  
  // analyze
  ssa_analyzert analyzer;
  analyzer.set_message_handler(get_message_handler());
  
  if(recursive)
  {
    exprt merge_expr;
    template_gen_rec_summaryt template_generator=template_gen_rec_summaryt(
    options, ssa_db, ssa_unwinder.get(function_name));
    template_generator.set_message_handler(get_message_handler());
    template_generator(function_name, solver.next_domain_number(),
     SSA, merge_expr, true);
    
    exprt precond(summary.fw_precondition);
    if(context_sensitive)
      replace_expr(template_generator.init_vars_map,precond);
    
    exprt::operandst conds;
    conds.reserve(5);
    conds.push_back(cond);
    conds.push_back(precond);
    conds.push_back(ssa_inliner.get_summaries(SSA));
    cond=conjunction(conds);
    
    analyzer(solver, SSA, cond, template_generator, true, merge_expr);
    analyzer.get_result(summary.fw_transformer, template_generator.inout_vars());
    analyzer.get_result(summary.fw_invariant, template_generator.loop_vars());
  }
  else
  {
    template_generator_summaryt template_generator=template_generator_summaryt(
    options, ssa_db, ssa_unwinder.get(function_name));
    template_generator.set_message_handler(get_message_handler());
    template_generator(solver.next_domain_number(),
     SSA, true);
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
  }
  
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
