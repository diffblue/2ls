/*******************************************************************\

Module: Summary Checker for k-induction

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Summary Checker for k-induction

#ifndef CPROVER_2LS_2LS_SUMMARY_CHECKER_KIND_H
#define CPROVER_2LS_2LS_SUMMARY_CHECKER_KIND_H

#include "summary_checker_base.h"

class summary_checker_kindt:public summary_checker_baset
{
public:
  inline summary_checker_kindt(
    optionst &_options,
    const ssa_heap_analysist &heap_analysis):
    summary_checker_baset(_options, heap_analysis)
  {
  }

  virtual resultt operator()(const goto_modelt &);
};

#endif
