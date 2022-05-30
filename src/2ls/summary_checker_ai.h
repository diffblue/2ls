/*******************************************************************\

Module: Summary Checker for AI

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Summary Checker for AI

#ifndef CPROVER_2LS_2LS_SUMMARY_CHECKER_AI_H
#define CPROVER_2LS_2LS_SUMMARY_CHECKER_AI_H

#include "summary_checker_base.h"

class summary_checker_ait:public summary_checker_baset
{
public:
  explicit inline summary_checker_ait(
    optionst &_options,
    goto_modelt &_goto_model):
    summary_checker_baset(_options, _goto_model) {}

  resultt operator()() override;

protected:
  void report_preconditions();
  resultt report_termination();
};

#endif
