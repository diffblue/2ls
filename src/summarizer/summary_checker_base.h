/*******************************************************************\

Module: Summary Checker Base

Author: Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_SUMMARY_CHECKER_BASE_H
#define CPROVER_SUMMARY_CHECKER_BASE_H

#include <util/time_stopping.h>

#include <goto-programs/property_checker.h>
#include <solvers/prop/prop_conv.h>

#include "cover_goals_ext.h"
#include "../ssa/local_ssa.h"
#include "../ssa/ssa_unwinder.h"
#include "../ssa/ssa_inliner.h"
#include "../domains/incremental_solver.h"
#include "ssa_db.h"
#include "summary_db.h"

class summary_checker_baset:public property_checkert
{
public:
  inline summary_checker_baset(optionst &_options):
    show_vcc(false),
    simplify(false),
    fixed_point(false),
    options(_options),
    ssa_db(_options),summary_db(),
    ssa_unwinder(ssa_db),
    ssa_inliner(summary_db),
    solver_instances(0),
    solver_calls(0),
    summaries_used(0)
  {
    ssa_inliner.set_message_handler(get_message_handler());
  }
  
  bool show_vcc, simplify, fixed_point;
  irep_idt function_to_check;

  virtual resultt operator()(const goto_modelt &) { assert(false); }

  void instrument_and_output(goto_modelt &goto_model);

  // statistics
  absolute_timet start_time;
  time_periodt sat_time;

protected:
  optionst &options;

  ssa_dbt ssa_db;
  summary_dbt summary_db;
  ssa_unwindert ssa_unwinder;
  ssa_inlinert ssa_inliner;

  unsigned solver_instances;
  unsigned solver_calls;
  unsigned summaries_used;
  void report_statistics();

  void do_show_vcc(
    const local_SSAt &,
    const goto_programt::const_targett,
    const local_SSAt::nodet::assertionst::const_iterator &);

  void SSA_functions(const goto_modelt &, const namespacet &ns);

  void summarize(const goto_modelt &, 
		 bool forward=true, bool termination=false);

  property_checkert::resultt check_properties();
  void check_properties(
		  const ssa_dbt::functionst::const_iterator f_it);

  exprt::operandst get_loophead_selects(
    const irep_idt &function_name, const local_SSAt &, prop_convt &);
  bool is_spurious(const exprt::operandst& loophead_selects, 
		   incremental_solvert&);
  exprt::operandst get_loop_continues(
    const irep_idt &function_name, const local_SSAt &, prop_convt &);
  bool is_fully_unwound(
    const exprt::operandst& loop_continues,
    const exprt::operandst& loophead_selects, 
    incremental_solvert&);
};

#endif
