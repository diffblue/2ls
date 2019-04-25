/*******************************************************************\

Module: Summary Checker for BMC

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Summary Checker for BMC

#ifndef CPROVER_2LS_2LS_SUMMARY_CHECKER_BMC_H
#define CPROVER_2LS_2LS_SUMMARY_CHECKER_BMC_H

#include "summary_checker_base.h"

class summary_checker_bmct:public summary_checker_baset
{
public:
  summary_checker_bmct(
    optionst &_options,
    const ssa_heap_analysist &heap_analysis):
    summary_checker_baset(_options, heap_analysis)
  {
  }

  virtual resultt operator()(const goto_modelt &);
};

#endif
