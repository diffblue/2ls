/*******************************************************************\

Module: Summarizer Base

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Summarizer Base

#include <iostream>

#include <util/simplify_expr.h>
#include <solvers/sat/satcheck.h>
#include <solvers/flattening/bv_pointers.h>
#include <solvers/smt2/smt2_dec.h>
#include <util/find_symbols.h>

#include "summarizer_base.h"
#include "summary_db.h"

#include <domains/ssa_analyzer.h>
#include <domains/template_generator_summary.h>
#include <domains/template_generator_callingcontext.h>

#include <ssa/local_ssa.h>
#include <ssa/simplify_ssa.h>


void summarizer_baset::summarize()
{
  exprt precondition=true_exprt(); // initial calling context
  for(functionst::const_iterator it=ssa_db.functions().begin();
      it!=ssa_db.functions().end(); it++)
  {
    status() << "\nSummarizing function " << it->first << eom;
    if(!summary_db.exists(it->first) ||
       summary_db.get(it->first).mark_recompute)
      compute_summary_rec(it->first, precondition, false);
    else
      status() << "Summary for function " << it->first
               << " exists already" << eom;
  }
}

/// summarize from given entry point
void summarizer_baset::summarize(const function_namet &function_name)
{
  exprt precondition=true_exprt(); // initial calling context

  status() << "\nSummarizing function " << function_name << eom;
  if(!summary_db.exists(function_name) ||
     summary_db.get(function_name).mark_recompute)
  {
    compute_summary_rec(
      function_name,
      precondition,
      options.get_bool_option("context-sensitive"));
  }
  else
    status() << "Summary for function " << function_name
             << " exists already" << eom;
}

/// returns false if function call is not reachable
bool summarizer_baset::check_call_reachable(
  const function_namet &function_name,
  local_SSAt &SSA,
  local_SSAt::nodest::const_iterator n_it,
  local_SSAt::nodet::function_callst::const_iterator f_it,
  const exprt& precondition,
  bool forward)
{
  assert(f_it->function().id()==ID_symbol); // no function pointers
  irep_idt fname=to_symbol_expr(f_it->function()).get_identifier();

  debug() << "Checking reachability of call to " << fname << eom;

  bool reachable=false;

  // reachability check
  incremental_solvert &solver=ssa_db.get_solver(function_name);
  solver.set_message_handler(get_message_handler());
  solver << SSA;
  SSA.mark_nodes();

  solver.new_context();
  solver << SSA.get_enabling_exprs();
  solver << precondition;
  solver << ssa_inliner.get_summaries(SSA);

  symbol_exprt guard=SSA.guard_symbol(n_it->location);
  ssa_unwinder.get(function_name).unwinder_rename(guard, *n_it, false);
  solver << guard;

#if 0
  std::cout << "guard: " << from_expr(SSA.ns, "", guard) << std::endl;
  std::cout << "enable: " << from_expr(SSA.ns, "", SSA.get_enabling_exprs())
            << std::endl;
  std::cout << "precondition: " << from_expr(SSA.ns, "", precondition)
            << std::endl;
  std::cout << "summaries: "
            << from_expr(SSA.ns, "", ssa_inliner.get_summaries(SSA))
            << std::endl;
#endif

  if(!forward)
    solver << SSA.guard_symbol(--SSA.goto_function.body.instructions.end());

  switch(solver())
  {
  case decision_proceduret::resultt::D_SATISFIABLE:
  {
    reachable=true;
    debug() << "Call is reachable" << eom;
    break;
  }
  case decision_proceduret::resultt::D_UNSATISFIABLE:
  {
    debug() << "Call is not reachable" << eom;
    break;
  }
  default: assert(false); break;
  }

  solver.pop_context();

  return reachable;
}

/// computes callee preconditions from the calling context for a single function
/// call
exprt summarizer_baset::compute_calling_context(
  const function_namet &function_name,
  local_SSAt &SSA,
  local_SSAt::nodest::const_iterator n_it,
  local_SSAt::nodet::function_callst::const_iterator f_it,
  const exprt &precondition,
  bool forward)
{
  assert(f_it->function().id()==ID_symbol); // no function pointers
  irep_idt fname=to_symbol_expr(f_it->function()).get_identifier();

  status() << "Computing calling context for function " << fname << eom;

  // solver
  incremental_solvert &solver=ssa_db.get_solver(function_name);
  solver.set_message_handler(get_message_handler());
  solver << SSA;
  SSA.mark_nodes();

  solver.new_context();
  solver << SSA.get_enabling_exprs();
  solver << ssa_inliner.get_summaries_to_loc(SSA, n_it->location);

  ssa_analyzert analyzer;
  analyzer.set_message_handler(get_message_handler());

  template_generator_callingcontextt template_generator(
    options, ssa_db, ssa_unwinder.get(function_name));
  template_generator.set_message_handler(get_message_handler());
  template_generator(solver.next_domain_number(), SSA, n_it, f_it, forward);

  // collect globals at call site
  std::map<local_SSAt::nodet::function_callst::const_iterator,
           local_SSAt::var_sett>
    cs_globals_in;
  if(forward)
    SSA.get_globals(n_it->location, cs_globals_in[f_it]);
  else
    SSA.get_globals(n_it->location, cs_globals_in[f_it], false);

  exprt cond=precondition;
  if(!forward)
    cond=and_exprt(
      cond, SSA.guard_symbol(--SSA.goto_function.body.instructions.end()));

  // analyze
  analyzer(solver, SSA, cond, template_generator);

  // set preconditions
  local_SSAt &fSSA=ssa_db.get(fname);

  preconditiont precondition_call;
  analyzer.get_result(
    precondition_call,
    template_generator.callingcontext_vars());
  ssa_inliner.rename_to_callee(
    f_it, fSSA.params, cs_globals_in[f_it], fSSA.globals_in, precondition_call);

  debug() << (forward ? "Forward " : "Backward ") << "calling context for "
          << from_expr(SSA.ns, "", *f_it) << ": "
          << from_expr(SSA.ns, "", precondition_call) << eom;

  // statistics
  solver_instances+=analyzer.get_number_of_solver_instances();
  solver_calls+=analyzer.get_number_of_solver_calls();

  solver.pop_context();

  return precondition_call;
}

void summarizer_baset::get_assertions(
  const local_SSAt &SSA,
  exprt::operandst &assertions)
{
  for(const auto &node : SSA.nodes)
    for(const auto &a : node.assertions)
      assertions.push_back(a);
}

/// returns false if the summary needs to be recomputed
bool summarizer_baset::check_precondition(
  const function_namet &function_name,
  local_SSAt &SSA,
  local_SSAt::nodest::const_iterator n_it,
  local_SSAt::nodet::function_callst::const_iterator f_it,
  const exprt &precondition,
  bool context_sensitive)
{
  assert(f_it->function().id()==ID_symbol); // no function pointers
  irep_idt fname=to_symbol_expr(f_it->function()).get_identifier();

  status() << "Checking precondition of " << fname << eom;

  bool precondition_holds=false;
  exprt assertion;

  if(summary_db.exists(fname))
  {
    const summaryt &summary=summary_db.get(fname);
    if(summary.mark_recompute)
      return false;
    if(!context_sensitive ||
       summary.fw_precondition.is_true())  // precondition trivially holds
    {
      status() << "Precondition trivially holds, replacing by summary."
               << eom;
      summaries_used++;
      precondition_holds=true;
    }
    else
    {
      assertion=summary.fw_precondition;

      // getting globals at call site
      local_SSAt::var_sett cs_globals_in;
      SSA.get_globals(n_it->location, cs_globals_in);

      ssa_inliner.rename_to_caller(
        f_it, summary.params, cs_globals_in, summary.globals_in, assertion);

      debug() << "precondition assertion: "
              << from_expr(SSA.ns, "", assertion) << eom;

      precondition_holds=false;
    }
  }
  else if(!ssa_db.exists(fname))
  {
    status() << "Function " << fname << " not found" << eom;
    precondition_holds=true;
  }
  else if(fname==function_name)
  {
    status() << "Havoc recursive function call to " << fname << eom;
    precondition_holds=true;
  }
  else
  {
    status() << "Function " << fname << " not analyzed yet" << eom;
    return false; // function not seen yet
  }

  if(precondition_holds)
    return true;

  assert(!assertion.is_nil());

  // precondition check
  // solver
  incremental_solvert &solver=ssa_db.get_solver(function_name);
  solver.set_message_handler(get_message_handler());
  solver << SSA;
  SSA.mark_nodes();

  solver.new_context();
  solver << SSA.get_enabling_exprs();

  solver << precondition;
  solver << ssa_inliner.get_summaries(SSA);

  // add precondition
  solver << not_exprt(assertion);

  switch(solver())
  {
  case decision_proceduret::resultt::D_SATISFIABLE:
  {
    precondition_holds=false;

    status() << "Precondition does not hold, need to recompute summary." << eom;
    break;
  }
  case decision_proceduret::resultt::D_UNSATISFIABLE:
  {
    precondition_holds=true;

    status() << "Precondition holds, replacing by summary." << eom;
    summaries_used++;

    break;
  }
  default: assert(false); break;
  }

  solver.pop_context();

  return precondition_holds;
}

/// returns false if the end of the function is not reachable
bool summarizer_baset::check_end_reachable(
  const function_namet &function_name,
  local_SSAt &SSA,
  const exprt &cond)
{
  incremental_solvert &solver=ssa_db.get_solver(function_name);
  solver.set_message_handler(get_message_handler());
  solver << SSA;
  SSA.mark_nodes();

  solver.new_context();
  solver << SSA.get_enabling_exprs();
  solver << ssa_inliner.get_summaries(SSA);

  solver << cond;

  exprt::operandst assertions;
  // do not add assertions
  //  because a failing assertion does not prove termination
  assertions.push_back(
    not_exprt(SSA.guard_symbol(--SSA.goto_function.body.instructions.end())));

  solver << not_exprt(conjunction(assertions)); // we want to reach any of them

  bool result=(solver()==decision_proceduret::resultt::D_SATISFIABLE);

  solver.pop_context();

  return result;
}
