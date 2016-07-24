/*******************************************************************\

Module: Summarizer for Backward Analysis

Author: Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_SUMMARIZER_BW_H
#define CPROVER_SUMMARIZER_BW_H

#include <util/message.h>
#include <util/options.h>
#include <util/time_stopping.h>

#include <ssa/ssa_inliner.h>
#include <ssa/ssa_unwinder.h>
#include <ssa/local_ssa.h>
#include <ssa/ssa_db.h>

#include "summarizer_base.h"

class summarizer_bwt : public summarizer_baset
{
 public:
 explicit summarizer_bwt(optionst &_options, 
	     summary_dbt &_summary_db,
             ssa_dbt &_ssa_db,
	     ssa_unwindert &_ssa_unwinder,
	     ssa_inlinert &_ssa_inliner) : 
  summarizer_baset(_options,_summary_db,_ssa_db,_ssa_unwinder,_ssa_inliner)
  {}

  virtual void summarize(); 
  virtual void summarize(const function_namet &entry_function); 


 protected:

  virtual void compute_summary_rec(const function_namet &function_name,
    		           const exprt &postcondition,
                           bool context_sensitive);

  void inline_summaries(const function_namet &function_name, 
			local_SSAt &SSA,
			const summaryt &old_summary,
    		        const exprt &postcondition,
                        bool context_sensitive,
			bool sufficient); 

  virtual void do_summary(const function_namet &function_name, 
		  local_SSAt &SSA, 
		  const summaryt &old_summary,
		  summaryt &summary, 
		  bool context_sensitive);

  virtual bool check_postcondition(const function_namet &function_name, 
                  const local_SSAt &SSA,
		  local_SSAt::nodest::const_iterator node, 
		  local_SSAt::nodet::function_callst::const_iterator f_it,
    		  const exprt &postcondition,
                  bool context_sensitive);

  virtual void collect_postconditions(const function_namet &function_name,
			      const local_SSAt &SSA, 
			      const summaryt &summary,
			      exprt::operandst &postconditions,
			      bool sufficient);

  virtual exprt compute_calling_context2(const function_namet &function_name, 
    local_SSAt &SSA,
    summaryt old_summary,
    local_SSAt::nodest::const_iterator n_it, 
    local_SSAt::nodet::function_callst::const_iterator f_it,
    const exprt &postcondition,
    bool sufficient);

};


#endif
