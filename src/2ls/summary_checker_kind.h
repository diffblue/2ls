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
  explicit inline summary_checker_kindt(
    optionst &_options,
    goto_modelt &_goto_model,
    dynamic_objectst &dynamic_objects):
    summary_checker_baset(_options, _goto_model, dynamic_objects) {}

  resultt operator()() override;
};

#endif
