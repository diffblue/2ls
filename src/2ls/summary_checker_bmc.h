/*******************************************************************\

Module: Summary Checker for BMC

Author: Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_2LS_2LS_SUMMARY_CHECKER_BMC_H
#define CPROVER_2LS_2LS_SUMMARY_CHECKER_BMC_H

#include "summary_checker_base.h"

class summary_checker_bmct:public summary_checker_baset
{
public:
  summary_checker_bmct(
    optionst &_options,
    message_handlert &_message_handler):
    summary_checker_baset(_options, _message_handler)
  {
  }

  virtual resultt operator()(const goto_modelt &);
};

#endif
