/*******************************************************************\

Module: Summarizer

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SUMMARY_CHECKER_H
#define CPROVER_SUMMARY_CHECKER_H

#include <util/time_stopping.h>

#include <goto-programs/property_checker.h>

#include "../ssa/local_ssa.h"

class summary_checkert:public property_checkert
{
public:
  inline summary_checkert():
    show_vcc(false),
    simplify(false),
    fixed_point(false)
  {
  }
  
  bool show_vcc, simplify, fixed_point;

  virtual resultt operator()(const goto_modelt &);

  // statistics
  absolute_timet start_time;
  time_periodt sat_time;

protected:
  void report_statistics();

  void do_show_vcc(
    const local_SSAt &,
    const goto_programt::const_targett);

  resultt check_properties(const goto_modelt &);

  void check_properties(
    const local_SSAt &,
    const goto_functionst::function_mapt::const_iterator f_it);
};

#endif
