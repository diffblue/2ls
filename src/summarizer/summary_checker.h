/*******************************************************************\

Module: Summarizer

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SUMMARY_CHECKER_H
#define CPROVER_SUMMARY_CHECKER_H

#include <util/time_stopping.h>

#include <goto-programs/safety_checker.h>

#include "../ssa/local_ssa.h"
#include "../ai/summarizer.h"

class summary_checkert:public safety_checkert
{
public:
  explicit inline summary_checkert(const namespacet &_ns, summarizert &_summarizer):
    safety_checkert(_ns),
    show_vcc(false),
    simplify(false),
    summarizer(_summarizer)
  {
  }
  
  bool show_vcc, simplify;

  virtual resultt operator()(
    const goto_functionst &goto_functions);

  // statistics
  absolute_timet start_time;
  time_periodt sat_time;

  enum statust { UNKNOWN, PASS, FAIL };

  struct property_entryt
  {
    statust status;
    irep_idt description;
    goto_tracet error_trace;
  };
  
  typedef std::map<irep_idt, property_entryt> property_mapt;
  property_mapt property_map;

protected:
  summarizert summarizer;

  void report_statistics();

  void initialize_property_map(
    const goto_functionst &goto_functions);

  void do_show_vcc(const local_SSAt &, const goto_programt::const_targett);

  resultt check_properties(
    const goto_functionst &goto_functions);

  void check_properties(
    const goto_functionst::function_mapt::const_iterator f_it);
  
};

#endif
