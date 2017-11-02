/*******************************************************************\

Module: Summary Checker for AI

Author: Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_2LS_2LS_SUMMARY_CHECKER_AI_H
#define CPROVER_2LS_2LS_SUMMARY_CHECKER_AI_H

#include "summary_checker_base.h"

class summary_checker_ait:public summary_checker_baset
{
public:
  explicit summary_checker_ait(
    optionst &_options,
    const ssa_heap_analysist &heap_analysis):
    summary_checker_baset(_options, heap_analysis)
  {
  }

  virtual resultt operator()(const goto_modelt &);

protected:
  void report_preconditions();
  property_checkert::resultt report_termination();
};

#endif
