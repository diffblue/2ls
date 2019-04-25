/*******************************************************************\

Module: Summarizer Base

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Summarizer Base

#ifndef CPROVER_2LS_SOLVER_SUMMARIZER_BASE_H
#define CPROVER_2LS_SOLVER_SUMMARIZER_BASE_H

#include <util/message.h>
#include <util/options.h>
#include <util/time_stopping.h>

#include <ssa/ssa_inliner.h>
#include <ssa/ssa_unwinder.h>
#include <ssa/local_ssa.h>
#include <ssa/ssa_db.h>

class summarizer_baset:public messaget
{
public:
  explicit summarizer_baset(
    optionst &_options,
    summary_dbt &_summary_db,
    ssa_dbt &_ssa_db,
    ssa_unwindert &_ssa_unwinder,
    ssa_inlinert &_ssa_inliner):
    options(_options),
    summary_db(_summary_db),
    ssa_db(_ssa_db),
    ssa_unwinder(_ssa_unwinder),
    ssa_inliner(_ssa_inliner),
    solver_instances(0),
    solver_calls(0),
    summaries_used(0),
    termargs_computed(0)
  {
  }

  typedef summaryt::predicatet preconditiont;
  typedef irep_idt function_namet;
  typedef local_SSAt function_bodyt;
  typedef std::map<function_namet, preconditiont> preconditionst;
  typedef ssa_dbt::functionst functionst;
  typedef functionst::value_type functiont;

  virtual void summarize();
  virtual void summarize(const function_namet &entry_function);

  unsigned get_number_of_solver_instances() { return solver_instances; }
  unsigned get_number_of_solver_calls() { return solver_calls; }
  unsigned get_number_of_summaries_used() { return summaries_used; }
  unsigned get_number_of_termargs_computed() { return termargs_computed; }

 protected:
  optionst &options;
  summary_dbt &summary_db;
  ssa_dbt &ssa_db;
  ssa_unwindert &ssa_unwinder;
  ssa_inlinert &ssa_inliner;

  virtual void compute_summary_rec(
    const function_namet &function_name,
    const exprt &precondition,
    bool context_sensitive)
  {
    assert(false);
  }

  bool check_call_reachable(
    const function_namet &function_name,
    local_SSAt &SSA,
    local_SSAt::nodest::const_iterator n_it,
    local_SSAt::nodet::function_callst::const_iterator f_it,
    const exprt& precondition,
    bool forward);

  virtual exprt compute_calling_context(
    const function_namet &function_name,
    local_SSAt &SSA,
    local_SSAt::nodest::const_iterator n_it,
    local_SSAt::nodet::function_callst::const_iterator f_it,
    const exprt &precondition,
    bool forward);

  virtual bool check_precondition(
    const function_namet &function_name,
    local_SSAt &SSA,
    local_SSAt::nodest::const_iterator node,
    local_SSAt::nodet::function_callst::const_iterator f_it,
    const exprt &precondition,
    bool context_sensitive);

  void get_assertions(
    const local_SSAt &SSA,
    exprt::operandst &assertions);

  bool check_end_reachable(
    const function_namet &function_name,
    local_SSAt &SSA,
    const exprt &cond);

  // statistics
  unsigned solver_instances;
  unsigned solver_calls;
  unsigned summaries_used;
  unsigned termargs_computed;
};


#endif
