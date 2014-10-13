/*******************************************************************\

Module: Summarizer

Author: Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_SUMMARIZER_H
#define CPROVER_SUMMARIZER_H

#include <util/message.h>
#include <util/options.h>
#include "../ssa/ssa_inliner.h"
#include "../ssa/ssa_unwinder.h"
#include "../ssa/local_ssa.h"
#include "ssa_db.h"

#include <util/time_stopping.h>

class summarizert : public messaget
{
 public:
 summarizert(optionst &_options, 
	     summary_dbt &_summary_db,
             ssa_dbt &_ssa_db,
	     ssa_unwindert &_ssa_unwinder,
	     ssa_inlinert &_ssa_inliner) : 
    options(_options),
    summary_db(_summary_db),
    ssa_db(_ssa_db),
    ssa_unwinder(_ssa_unwinder),
    ssa_inliner(_ssa_inliner),
    solver_instances(0),
    solver_calls(0),
    summaries_used(0)
  {}

  typedef summaryt::predicatet preconditiont;
  typedef irep_idt function_namet;
  typedef local_SSAt function_bodyt;
  typedef std::map<function_namet, preconditiont> preconditionst;
  typedef ssa_dbt::functionst functionst;
  typedef functionst::value_type functiont;

  void summarize(bool forward, bool sufficient); 

  void summarize(const function_namet &entry_function,
                 bool forward, bool sufficient); 

  unsigned get_number_of_solver_instances() { return solver_instances; }
  unsigned get_number_of_solver_calls() { return solver_calls; }
  unsigned get_number_of_summaries_used() { return summaries_used; }

 protected:
  optionst &options;
  summary_dbt &summary_db;
  ssa_dbt &ssa_db;
  ssa_unwindert &ssa_unwinder;
  ssa_inlinert &_ssa_inliner;

  void compute_summary_rec(const function_namet &function_name,
    		           const exprt &precondition,
                           bool context_sensitive, 
			   bool forward,
                           bool sufficient);

  void join_summaries(const summaryt &existing_summary, summaryt &new_summary);

  void inline_summaries(const function_namet &function_name, 
			local_SSAt &SSA,
    		        const exprt &fw_precondition,
                        bool context_sensitive, bool forward, bool sufficient,
			threevalt &calls_terminate, bool &has_function_calls); 

  bool check_precondition(const function_namet &function_name, 
			  local_SSAt::nodest::iterator node, 
			  local_SSAt::nodet::function_callst::iterator f_it,
                          local_SSAt &SSA,
    		          const exprt &fw_precondition,
                          ssa_inlinert &inliner,
			  bool forward,
			  bool sufficient);

  bool check_call_reachable(
    const function_namet &function_name,
    const exprt &fw_precondition,
    local_SSAt::nodest::iterator n_it, 
    local_SSAt::nodet::function_callst::iterator f_it,
    local_SSAt &SSA);

  //computes precondition in caller context
  exprt compute_calling_context(const function_namet &function_name, 
			    local_SSAt::nodest::iterator node, 
			    local_SSAt::nodet::function_callst::iterator f_it,
			    local_SSAt &SSA,
    		            const exprt &fw_precondition,
                            ssa_inlinert &inliner,
                            bool forward);

  void do_summary(const function_namet &function_name, 
		  local_SSAt &SSA, 
                  const exprt &fw_precondition,
		  summaryt &summary, 
		  bool forward, bool sufficient);
  void do_termination(const function_namet &function_name, 
		      local_SSAt &SSA, 
		      const exprt &fw_precondition,
		      summaryt &summary);
  void do_termination_preconditions_only(const function_namet &function_name, 
		      local_SSAt &SSA, 
                      const exprt &fw_precondition,
		      summaryt &summary);
  void do_termination_with_preconditions(const function_namet &function_name, 
		      local_SSAt &SSA, 
                      const exprt &fw_precondition,
		      summaryt &summary);
  threevalt check_termination_argument(exprt expr);

  exprt collect_postconditions(const function_namet &function_name,
			       const local_SSAt &SSA, 
			       const summaryt &summary,
			       bool forward,
			       bool sufficient,
			       bool termination,
			       exprt::operandst &postconditions);

  bool check_end_reachable(const function_namet &function_name,
			   const local_SSAt &SSA, 
			   const exprt &fw_precondition,
			   const summaryt &summary);

  exprt assertions_to_assumptions(const local_SSAt &SSA);

  //statistics
  unsigned solver_instances;
  unsigned solver_calls;
  unsigned summaries_used;
};


#endif
