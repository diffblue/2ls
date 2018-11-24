/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/* 
 * File:   summary_checker_rect.cpp
 * Author: sarbojit
 * 
 * Created on 21 March, 2018, 7:13 PM
 */

#include <solver/summarizer_fw.h>
#include <solver/summarizer_fw_term.h>
#include <solver/summarizer_bw.h>
#include <solver/summarizer_bw_term.h>
#include <solver/summarizer_rec_fw.h>

#include "summary_checker_rect.h"

property_checkert::resultt summary_checker_rect::operator()(
  const goto_modelt &goto_model)
{
  const namespacet ns(goto_model.symbol_table);

  SSA_functions(goto_model, ns, heap_analysis);

  ssa_unwinder.init(false, false);

  unsigned unwind=options.get_unsigned_int_option("unwind");
  if(unwind>0)
  {
    status() << "Unwinding" << messaget::eom;

    ssa_unwinder.init_localunwinders();

    ssa_unwinder.unwind_all(unwind);
  }

  // properties
  initialize_property_map(goto_model.goto_functions);

  property_checkert::resultt result=property_checkert::UNKNOWN;
  bool finished=false;
  while(!finished)
  {
    bool preconditions=options.get_bool_option("preconditions");
    bool termination=options.get_bool_option("termination");
    bool trivial_domain=options.get_bool_option("havoc");
    if(!trivial_domain || termination)
    {
      // forward analysis
      summarize(goto_model, true, termination);
    }
    if(!trivial_domain && preconditions)
    {
      status()<<"No backward analysis supported for recursive programs."<<eom;
      exit(1);
    }

    if(preconditions)
    {
      report_statistics();
      report_preconditions();
      return property_checkert::UNKNOWN;
    }

    if(termination)
    {
      report_statistics();
      return report_termination();
    }

#ifdef SHOW_CALLINGCONTEXTS
    if(options.get_bool_option("show-calling-contexts"))
      return property_checkert::UNKNOWN;
#endif

  if(result==property_checkert::UNKNOWN &&
       options.get_bool_option("heap-values-refine") &&
       options.get_bool_option("heap-interval"))
    {
      summary_db.clear();
      options.set_option("heap-interval", false);
      options.set_option("heap-zones", true);
    }
    else
    {
      finished=true;
    }
  }
  //return result;
  return UNKNOWN;
}

void summary_checker_rect::summarize(
  const goto_modelt &goto_model,
  bool forward,
  bool termination)
{
  summarizer_baset *summarizer=NULL;
#ifdef SHOW_CALLING_CONTEXTS
  if(options.get_bool_option("show-calling-contexts"))
    summarizer=new summarizer_fw_contextst(
      options, summary_db, ssa_db, ssa_unwinder, ssa_inliner);
  else // NOLINT(*)
#endif
  {
    if(!termination)
      summarizer=new summarizer_rec_fwt(
        options, summary_db, ssa_db, ssa_unwinder, ssa_inliner);
    else
    {
      status()<<"No termination check supported for recursive programs."<<eom;
      exit(1);
    }
  }
  assert(summarizer!=NULL);
  summarizer->set_message_handler(get_message_handler());
  if(!options.get_bool_option("context-sensitive") &&
     options.get_bool_option("all-functions"))
    summarizer->summarize();
  else
    summarizer->summarize(goto_model.goto_functions.entry_point());

  // statistics
  solver_instances+=summarizer->get_number_of_solver_instances();
  solver_calls+=summarizer->get_number_of_solver_calls();
  summaries_used+=summarizer->get_number_of_summaries_used();
  termargs_computed+=summarizer->get_number_of_termargs_computed();

  delete summarizer;
}
