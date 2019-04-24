/*******************************************************************\

Module: Summarizer for Backward Analysis with Termination

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Summarizer for Backward Analysis with Termination

#ifndef CPROVER_2LS_SOLVER_SUMMARIZER_BW_TERM_H
#define CPROVER_2LS_SOLVER_SUMMARIZER_BW_TERM_H

#include <util/message.h>
#include <util/options.h>
#include <util/time_stopping.h>

#include <ssa/ssa_inliner.h>
#include <ssa/ssa_unwinder.h>
#include <ssa/local_ssa.h>
#include <ssa/ssa_db.h>
#include <domains/template_generator_summary.h>
#include <domains/template_generator_ranking.h>

#include "summarizer_bw.h"

class summarizer_bw_termt:public summarizer_bwt
{
public:
  explicit summarizer_bw_termt(
    optionst &_options,
    summary_dbt &_summary_db,
    ssa_dbt &_ssa_db,
    ssa_unwindert &_ssa_unwinder,
    ssa_inlinert &_ssa_inliner):
    summarizer_bwt(_options, _summary_db, _ssa_db, _ssa_unwinder, _ssa_inliner)
  {
  }

protected:
  virtual void compute_summary_rec(
    const function_namet &function_name,
    const exprt &postcondition,
    bool context_sensitive);

  void do_summary_term(
    const function_namet &function_name,
    local_SSAt &SSA,
    const summaryt &old_summary,
    summaryt &summary,
    bool context_sensitive);

  void do_nontermination(
    const function_namet &function_name,
    local_SSAt &SSA,
    const summaryt &old_summary,
    summaryt &summary);

  bool bootstrap_preconditions(
    local_SSAt &SSA,
    summaryt &summary,
    incremental_solvert &solver,
    template_generator_rankingt &template_generator1,
    template_generator_summaryt &template_generator2,
    exprt &termination_argument);

  exprt compute_termination_argument(
    local_SSAt &SSA,
    const exprt &precondition,
    incremental_solvert &solver,
    template_generator_rankingt &template_generator);

  exprt compute_precondition(
    local_SSAt &SSA,
    summaryt &summary,
    const exprt::operandst &postconditions,
    incremental_solvert &solver,
    template_generator_summaryt &template_generator,
    bool context_sensitive);
};

#endif
