/*******************************************************************\

Module: Summarizer for Termination Analysis

Author: Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_SUMMARIZER_TERM_H
#define CPROVER_SUMMARIZER_TERM_H

#include <util/message.h>
#include <util/options.h>

#include "summarizer_base.h"

#include "../ssa/ssa_inliner.h"
#include "../ssa/ssa_unwinder.h"
#include "../ssa/local_ssa.h"
#include "ssa_db.h"

#include <util/time_stopping.h>

class summarizer_termt : public summarizer_baset
{
 public:
 explicit summarizer_termt(optionst &_options, 
	     summary_dbt &_summary_db,
             ssa_dbt &_ssa_db,
	     ssa_unwindert &_ssa_unwinder,
	     ssa_inlinert &_ssa_inliner) : 
  summarizer_baset(_options,_summary_db,_ssa_db,_ssa_unwinder,_ssa_inliner)
  {}

  virtual void summarize(); 
  virtual void summarize(const function_namet &entry_function) 
    { assert(false); } //function does not make sense

 protected:

  virtual void compute_summary_rec(const function_namet &function_name,
    		           const exprt &precondition,
                           bool context_sensitive);

  void do_termination(const function_namet &function_name, 
		      const local_SSAt &SSA, 
		      const summaryt &old_summary,
		      summaryt &summary);

  threevalt check_termination_argument(exprt expr);

  bool check_end_reachable(const function_namet &function_name,
			   const local_SSAt &SSA, 
			   const exprt &cond);
};


#endif
