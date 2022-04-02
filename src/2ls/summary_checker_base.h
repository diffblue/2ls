/*******************************************************************\

Module: Summary Checker Base

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Summary Checker Base

#ifndef CPROVER_2LS_2LS_SUMMARY_CHECKER_BASE_H
#define CPROVER_2LS_2LS_SUMMARY_CHECKER_BASE_H

#include <solvers/prop/prop_conv.h>
#include <goto-checker/properties.h>
#include <goto-checker/goto_trace_storage.h>
#include <util/ui_message.h>
#include <util/make_unique.h>

#include <ssa/local_ssa.h>
#include <ssa/unwinder.h>
#include <ssa/ssa_unwinder.h>
#include <ssa/goto_unwinder.h>
#include <ssa/ssa_inliner.h>
#include <domains/incremental_solver.h>
#include <ssa/ssa_db.h>
#include <solver/summary_db.h>

#include "cover_goals_ext.h"
#include "traces.h"

class graphml_witness_extt;


class summary_checker_baset:public messaget
{
public:
  summary_checker_baset(
    optionst &_options,
    goto_modelt &_goto_model):
    show_vcc(false),
    simplify(false),
    fixed_point(false),
    options(_options),
    goto_model(_goto_model),
    ssa_db(_options), summary_db(),
    ssa_unwinder(util_make_unique<ssa_unwindert>(ssa_db)),
    ssa_inliner(summary_db),
    solver_instances(0),
    solver_calls(0),
    summaries_used(0),
    termargs_computed(0)
  {
    if(options.get_bool_option("unwind-goto"))
      ssa_unwinder=util_make_unique<goto_unwindert>(
        ssa_db,
        goto_model,
        simplify);
  }

  bool show_vcc, simplify, fixed_point;
  irep_idt function_to_check;

  virtual resultt operator()() { assert(false); }

  void instrument_and_output(
    goto_modelt &goto_model,
    ui_message_handlert &ui_message_handler,
    unsigned verbosity);

  void set_message_handler(message_handlert &_message_handler) override
  {
    messaget::set_message_handler(_message_handler);
    ssa_inliner.set_message_handler(_message_handler);
    ssa_db.set_message_handler(_message_handler);
  }

  propertiest property_map;

  tracest traces;

protected:
  optionst &options;

  goto_modelt &goto_model;
  ssa_dbt ssa_db;
  summary_dbt summary_db;
  std::unique_ptr<unwindert> ssa_unwinder;
  ssa_inlinert ssa_inliner;

  unsigned solver_instances;
  unsigned solver_calls;
  unsigned summaries_used;
  unsigned termargs_computed;
  void report_statistics();

  void do_show_vcc(
    const local_SSAt &,
    const goto_programt::const_targett,
    const local_SSAt::nodet::assertionst::const_iterator &);

  void SSA_functions(
    const goto_modelt &,
    const symbol_tablet &symbol_table);

  void summarize(
    const goto_modelt &,
    bool forward=true,
    bool termination=false);

  resultt check_properties();
  virtual void check_properties(
    const ssa_dbt::functionst::const_iterator f_it);

  exprt::operandst get_loophead_selects(
    const irep_idt &function_name,
    const local_SSAt &,
    prop_conv_solvert &);
  bool is_spurious(
    const exprt::operandst& loophead_selects,
    incremental_solvert&);
  exprt::operandst get_loop_continues(
    const irep_idt &function_name,
    const local_SSAt &,
    prop_convt &);
  bool is_fully_unwound(
    const exprt::operandst& loop_continues,
    const exprt::operandst& loophead_selects,
    incremental_solvert&);

  // FIXME: This is a backwards-compatible hack. CPROVER introduced property
  //        status NOT_CHECKED (previously there was only UNKNOWN). Adjust
  //        2LS to also differentiate between unknown properties and properties
  //        that were not checked at all.
  inline void set_properties_unknown()
  {
    for(auto &property : property_map)
      if(property.second.status==property_statust::NOT_CHECKED)
        property.second.status=property_statust::UNKNOWN;
  }

  friend graphml_witness_extt;
};

#endif
