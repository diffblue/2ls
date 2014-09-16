/*******************************************************************\

Module: Summarizer

Author: Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_SUMMARIZER_H
#define CPROVER_SUMMARIZER_H

#include <util/message.h>
#include <util/options.h>
#include "../ssa/ssa_inliner.h"
#include "../ssa/local_ssa.h"

#include <util/time_stopping.h>

class summarizert : public messaget
{
 public:
 summarizert(const optionst &_options, summary_dbt &_summary_db) : 
    options(_options),
    summary_db(_summary_db),
    solver_instances(0),
    solver_calls(0),
    summaries_used(0)
  {}

  typedef summaryt::predicatet preconditiont;
  typedef irep_idt function_namet;
  typedef local_SSAt function_bodyt;
  typedef std::map<function_namet, preconditiont> preconditionst;
  typedef std::map<function_namet, function_bodyt*> functionst;
  typedef functionst::value_type functiont;

  void summarize(functionst &functions,
                 bool forward, bool sufficient); 

  void summarize(functionst &functions, 
                 const function_namet &entry_function,
                 bool forward, bool sufficient); 

  unsigned get_number_of_solver_instances() { return solver_instances; }
  unsigned get_number_of_solver_calls() { return solver_calls; }
  unsigned get_number_of_summaries_used() { return summaries_used; }

 protected:
  const optionst &options;
  summary_dbt &summary_db;
  functionst functions;
  preconditionst preconditions;

  void compute_summary_rec(const function_namet &function_name,
                           bool context_sensitive, bool forward,
                           bool sufficient);

  void join_summaries(const summaryt &existing_summary, summaryt &new_summary);

  void inline_summaries(const function_namet &function_name, local_SSAt &SSA,
                        bool context_sensitive, bool forward, bool sufficient,
			bool &calls_terminate); 

  bool check_precondition(const function_namet &function_name, 
			  local_SSAt::nodest::iterator node, 
			  local_SSAt::nodet::function_callst::iterator f_it,
                          local_SSAt &SSA,
                          ssa_inlinert &inliner);

  //computes precondition in caller context
  void compute_precondition(const function_namet &function_name, 
			    local_SSAt::nodest::iterator node, 
			    local_SSAt::nodet::function_callst::iterator f_it,
			    local_SSAt &SSA,
                            ssa_inlinert &inliner,
                            bool forward);

  void initialize_preconditions(functionst &_functions, 
				bool forward, 
				bool sufficient);

  bool check_termination_argument(exprt expr);

  //statistics
  unsigned solver_instances;
  unsigned solver_calls;
  unsigned summaries_used;
};


#endif
