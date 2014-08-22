/*******************************************************************\

Module: Summarizer

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SUMMARY_CHECKER_H
#define CPROVER_SUMMARY_CHECKER_H

#include <util/time_stopping.h>

#include <goto-programs/property_checker.h>

#include "../ssa/local_ssa.h"
#include "ssa_db.h"
#include "summary_db.h"
#include "summarizer.h"

class summary_checkert:public property_checkert
{
public:
  inline summary_checkert(optionst &_options):
    show_vcc(false),
    simplify(false),
    fixed_point(false),
    options(_options),
    ssa_db(),summary_db(),
    summarizer(_options,summary_db),
    solver_instances(0),
    solver_calls(0)
  {
  }
  
  bool show_vcc, simplify, fixed_point;

  virtual resultt operator()(const goto_modelt &);

  // statistics
  absolute_timet start_time;
  time_periodt sat_time;

protected:
  optionst &options;

  ssa_dbt ssa_db;
  summary_dbt summary_db;
  summarizert summarizer;

  unsigned solver_instances;
  unsigned solver_calls;
  void report_statistics();

  void do_show_vcc(
    const local_SSAt &,
    const goto_programt::const_targett,
    const local_SSAt::nodet::assertionst::const_iterator &);

  void SSA_functions(const goto_modelt &, const namespacet &ns);

  void summarize(const goto_modelt &);

  property_checkert::resultt check_properties();
  void check_properties_non_incremental(const summarizert::functionst::const_iterator f_it);
  void check_properties_incremental(const summarizert::functionst::const_iterator f_it);

};

#endif
