/*******************************************************************\

Module: Summarizer for Backward Analysis with Termination

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Summarizer for Backward Analysis with Termination

#ifdef DEBUG
#include <iostream>
#endif

#include <util/simplify_expr.h>
#include <solvers/sat/satcheck.h>
#include <solvers/flattening/bv_pointers.h>
#include <solvers/smt2/smt2_dec.h>
#include <util/find_symbols.h>

#include <domains/ssa_analyzer.h>
#include <domains/template_generator_callingcontext.h>

#include <ssa/local_ssa.h>
#include <ssa/simplify_ssa.h>

#include "summarizer_bw_term.h"
#include "summarizer_fw_term.h"
#include "summary_db.h"

#define MAX_PRECONDITION_DISJUNCTS 5
#define MAX_BOOTSTRAP_ATTEMPTS 20

void summarizer_bw_termt::compute_summary_rec(
  const function_namet &function_name,
  const exprt &postcondition,
  bool context_sensitive)
{
  local_SSAt &SSA=ssa_db.get(function_name);

  const summaryt &old_summary=summary_db.get(function_name);

  // recursively compute summaries for function calls
  inline_summaries(
    function_name, SSA, old_summary, postcondition, context_sensitive, false);

  status() << "Analyzing function "  << function_name << eom;

  bool has_loops=false;
  for(local_SSAt::nodest::iterator n_it=SSA.nodes.begin();
      n_it!=SSA.nodes.end(); n_it++)
  {
    if(n_it->loophead!=SSA.nodes.end())
    {
      has_loops=true;
      break;
    }
  }

  debug() << "function " <<
    (has_loops ? "has loops" : "does not have loops") << eom;

  // create summary
  summaryt summary;
  summary.params=SSA.params;
  summary.globals_in=SSA.globals_in;
  summary.globals_out=SSA.globals_out;
  summary.bw_postcondition=postcondition;

  do_nontermination(function_name, SSA, old_summary, summary);
  if(!options.get_bool_option("havoc") &&
     summary.terminates!=NO)
  {
    if(!has_loops)
    {
      do_summary(function_name, SSA, old_summary, summary, context_sensitive);
    }
    else
    {
      do_summary_term(
        function_name, SSA, old_summary, summary, context_sensitive);
    }
  }

  // store summary in db
  summary_db.put(function_name, std::move(summary));

  {
    std::ostringstream out;
    out << std::endl << "Summary for function " << function_name << std::endl;
    summary_db.get(function_name).output(out, SSA.ns);
    status() << out.str() << eom;
  }
}

void summarizer_bw_termt::do_nontermination(
  const function_namet &function_name,
  local_SSAt &SSA,
  const summaryt &old_summary,
  summaryt &summary)
{
  // calling context, invariant, function call summaries
  exprt::operandst cond;
  cond.push_back(old_summary.fw_invariant);
  cond.push_back(old_summary.fw_precondition);
  cond.push_back(ssa_inliner.get_summaries(SSA));
  ssa_inliner.get_summaries(SSA, false, cond, cond); // backward summaries

  if(!check_end_reachable(function_name, SSA, conjunction(cond)))
  {
    status() << "Function never terminates" << eom;
    summary.bw_transformer=false_exprt();
    summary.bw_precondition=false_exprt();
    summary.terminates=NO;
  }
}

void summarizer_bw_termt::do_summary_term(
  const function_namet &function_name,
  local_SSAt &SSA,
  const summaryt &old_summary,
  summaryt &summary,
  bool context_sensitive)
{
  status() << "Computing preconditions for termination" << eom;

  // solver
  incremental_solvert &solver=ssa_db.get_solver(function_name);
  solver.set_message_handler(get_message_handler());

  // templates for ranking functions
  template_generator_rankingt template_generator1(
    options, ssa_db, ssa_unwinder.get(function_name));
  template_generator1.set_message_handler(get_message_handler());
  template_generator1(solver.next_domain_number(), SSA, true);

  // templates for backward summary
  template_generator_summaryt template_generator2(
    options, ssa_db, ssa_unwinder.get(function_name));
  template_generator2.set_message_handler(get_message_handler());
  template_generator2(solver.next_domain_number(), SSA, false);

  exprt::operandst bindings;
  exprt::operandst postcond;
  // backward summaries
  ssa_inliner.get_summaries(SSA, false, postcond, bindings);
  collect_postconditions(
    function_name,
    SSA,
    summary.bw_postcondition,
    postcond,
    true);

  // prepare solver
  solver << SSA;
  solver.new_context();
  solver << SSA.get_enabling_exprs();
  solver << old_summary.fw_precondition;
  solver << old_summary.fw_invariant;
  solver << ssa_inliner.get_summaries(SSA); // forward summaries
  solver << conjunction(bindings); // bindings for backward summaries

#if 0
  // compute preconditions individually
  // TODO: this should be done more transparently
  for(unsigned i=0; i<postcond.size(); i++)
  {
    exprt::operandst postcond2;
    postcond2.push_back(postcond[i]);
    compute_precondition(
      SSA, summary, postcond2, solver, template_generator2, context_sensitive);
  }
  postcond.clear();
#endif

  if(template_generator1.all_vars().empty())
  {
    compute_precondition(
      SSA, summary, postcond, solver, template_generator2, context_sensitive);
    solver.pop_context();
    return;
  }

  summary.bw_precondition=false_exprt(); // initialize
  unsigned number_disjuncts=0;
  while(number_disjuncts++<MAX_PRECONDITION_DISJUNCTS)
  {
    // bootstrap preconditions
    exprt termination_argument;
    if(!bootstrap_preconditions(
         SSA,
         summary,
         solver,
         template_generator1,
         template_generator2,
         termination_argument))
    {
      break;
    }

    // compute precondition
    // compute for individual termination arguments separately
    // TODO: this should be done more transparently
    if(termination_argument.id()==ID_and)
    {
      for(unsigned i=0; i<termination_argument.operands().size(); i++)
      {
        postcond.push_back(termination_argument.operands()[i]);

        exprt precondition=
          compute_precondition(
            SSA,
            summary,
            postcond,
            solver,
            template_generator2,
            context_sensitive);

        // join results
        if(summary.termination_argument.is_nil())
        {
          summary.termination_argument=
            implies_exprt(precondition, termination_argument);
        }
        else
        {
          summary.termination_argument=
            and_exprt(
              summary.termination_argument,
              implies_exprt(precondition, termination_argument));
        }

        // TODO: this is a bit asymmetric:
        //  the first precondition is joined with all other sources
        //  of non-termination (calls, bw calling context)
        postcond.clear();
      }
    }
    else // do not split termination arguments
    {
      postcond.push_back(termination_argument);
      exprt precondition=
        compute_precondition(
          SSA,
          summary,
          postcond,
          solver,
          template_generator2,
          context_sensitive);

      // join results
      if(summary.termination_argument.is_nil())
      {
        summary.termination_argument=
          implies_exprt(precondition, termination_argument);
      }
      else
      {
        summary.termination_argument=
          and_exprt(
            summary.termination_argument,
            implies_exprt(precondition, termination_argument));
      }

      // TODO: this is a bit asymmetric:
      //  the first precondition is joined with all other sources
      //  of non-termination (calls, bw calling context)
      postcond.clear();
    }
  }
  summary.bw_domain_ptr=template_generator2.get_domain();
  solver.pop_context();
}

bool summarizer_bw_termt::bootstrap_preconditions(
  local_SSAt &SSA,
  summaryt &summary,
  incremental_solvert &solver,
  template_generator_rankingt &template_generator1,
  template_generator_summaryt &template_generator2,
  exprt &termination_argument)
{
  // bootstrap with a concrete model for input variables
  const var_sett &invars=template_generator2.out_vars();
  solver.new_context();

  unsigned number_bootstraps=0;
  termination_argument=true_exprt();
  exprt::operandst checked_candidates;
  while(number_bootstraps++<MAX_BOOTSTRAP_ATTEMPTS)
  {
    // find new ones
    solver << not_exprt(summary.bw_precondition);
    // last node should be reachable
    solver << SSA.guard_symbol(--SSA.goto_function.body.instructions.end());

    // statistics
    solver_calls++;

    // solve
    exprt precondition;
    if(solver()==decision_proceduret::resultt::D_SATISFIABLE)
    {
      exprt::operandst c;
      for(var_sett::const_iterator it=invars.begin();
          it!=invars.end(); it++)
      {
        c.push_back(equal_exprt(*it, solver.solver->get(*it)));
      }
      precondition=conjunction(c);
      debug() << "bootstrap model for precondition: "
              << from_expr(SSA.ns, "", precondition) << eom;
      solver.pop_context();
    }
    else // whole precondition space covered
    {
      solver.pop_context();
      break;
    }

    termination_argument=
      compute_termination_argument(
        SSA, precondition, solver, template_generator1);

    if(summarizer_fw_termt::check_termination_argument(
         termination_argument)==YES)
    {
      return true;
    }

    solver.new_context();
    checked_candidates.push_back(precondition);
    solver << not_exprt(disjunction(checked_candidates)); // next one, please!
  }

  return false;
}

exprt summarizer_bw_termt::compute_termination_argument(
  local_SSAt &SSA,
  const exprt &precondition,
  incremental_solvert &solver,
  template_generator_rankingt &template_generator)
{
  // compute ranking functions
  ssa_analyzert analyzer;
  analyzer.set_message_handler(get_message_handler());
  analyzer(solver, SSA, precondition, template_generator);
  exprt termination_argument;
  analyzer.get_result(termination_argument, template_generator.all_vars());

  // statistics
  solver_instances+=analyzer.get_number_of_solver_instances();
  solver_calls+=analyzer.get_number_of_solver_calls();
  termargs_computed++;

  return termination_argument;
}

exprt summarizer_bw_termt::compute_precondition(
  local_SSAt &SSA,
  summaryt &summary,
  const exprt::operandst &postconditions,
  incremental_solvert &solver,
  template_generator_summaryt &template_generator,
  bool context_sensitive)
{
  exprt postcond=not_exprt(conjunction(postconditions));

  // compute backward summary
  summaryt bw_summary;
  exprt bw_transformer, bw_invariant, bw_precondition;
  if(!template_generator.out_vars().empty())
  {
    ssa_analyzert analyzer;
    analyzer.set_message_handler(get_message_handler());
    analyzer(solver, SSA, postcond, template_generator);
    analyzer.get_result(bw_transformer, template_generator.inout_vars());
    analyzer.get_result(bw_invariant, template_generator.loop_vars());
    analyzer.get_result(bw_precondition, template_generator.out_vars());
    summary.bw_value_ptr=analyzer.get_abstract_value();

    // statistics
    solver_instances+=analyzer.get_number_of_solver_instances();
    solver_calls+=analyzer.get_number_of_solver_calls();
  }
#if 1
  // TODO: yet another workaround for ssa_analyzer
  //  not being able to handle empty templates properly
  else
  {
    solver << SSA;
    solver.new_context();
    solver << SSA.get_enabling_exprs();
    solver << postcond;
    exprt result=true_exprt();
    if(solver()==decision_proceduret::resultt::D_UNSATISFIABLE)
      result=false_exprt();
    solver.pop_context();
    bw_transformer=result;
    bw_invariant=result;
    bw_precondition=result;
  }
#endif

  bw_transformer=not_exprt(bw_transformer);
  bw_invariant=not_exprt(bw_invariant);
  bw_precondition=not_exprt(bw_precondition);

  if(context_sensitive && !summary.bw_postcondition.is_true())
  {
    bw_transformer=implies_exprt(summary.bw_postcondition, bw_transformer);
    bw_invariant=implies_exprt(summary.bw_postcondition, bw_invariant);
    bw_precondition=implies_exprt(summary.bw_postcondition, bw_precondition);
  }

  // join // TODO: should go into summaryt
  if(summary.bw_transformer.is_nil())
  {
    summary.bw_transformer=bw_transformer;
    summary.bw_invariant=bw_invariant;
    summary.bw_precondition=bw_precondition;
  }
  else
  {
    summary.bw_transformer=or_exprt(summary.bw_transformer, bw_transformer);
    summary.bw_invariant=or_exprt(summary.bw_invariant, bw_invariant);
    summary.bw_precondition=or_exprt(summary.bw_precondition, bw_precondition);
  }
  summary.bw_value_ptr=std::move(bw_summary.bw_value_ptr);

  return bw_precondition;
}


