/*******************************************************************\

Module: Summarizer for Forward Analysis

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Summarizer for Forward Analysis

#ifndef CPROVER_2LS_SOLVER_SUMMARIZER_FW_H
#define CPROVER_2LS_SOLVER_SUMMARIZER_FW_H

#include <util/message.h>
#include <util/options.h>
#include <util/time_stopping.h>

#include <ssa/ssa_inliner.h>
#include <ssa/ssa_unwinder.h>
#include <ssa/local_ssa.h>
#include <ssa/ssa_db.h>

#include "summarizer_base.h"

class summarizer_fwt:public summarizer_baset
{
public:
  summarizer_fwt(
    optionst &options,
    summary_dbt &summary_db,
    ssa_dbt &ssa_db,
    ssa_unwindert &ssa_unwinder,
    ssa_inlinert &ssa_inliner):
    summarizer_baset(options, summary_db, ssa_db, ssa_unwinder, ssa_inliner)
  {
  }

protected:
  virtual void compute_summary_rec(
    const function_namet &function_name,
    const exprt &precondition,
    bool context_sensitive);

  void inline_summaries(
    const function_namet &function_name,
    local_SSAt &SSA,
    const exprt &precondition,
    bool context_sensitive);

  void do_summary(
    const function_namet &function_name,
    local_SSAt &SSA,
    summaryt &summary,
    exprt cond, // additional constraints
    bool forward);
};

#endif
