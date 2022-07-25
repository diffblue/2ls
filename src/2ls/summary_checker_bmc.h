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
  explicit summary_checker_bmct(
    optionst &_options,
    goto_modelt &_goto_model,
    dynamic_objectst &dynamic_objects):
    summary_checker_baset(_options, _goto_model, dynamic_objects) {}

  resultt operator()() override;
};

#endif
