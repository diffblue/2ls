/*******************************************************************\

Module: Summary Checker for k-induction

Author: Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_2LS_2LS_SUMMARY_CHECKER_KIND_H
#define CPROVER_2LS_2LS_SUMMARY_CHECKER_KIND_H

#include "summary_checker_base.h"

class summary_checker_kindt:public summary_checker_baset
{
public:
  summary_checker_kindt(
    optionst &_options,
    message_handlert &_message_handler):
    summary_checker_baset(_options, _message_handler)
  {
  }

  virtual resultt operator()(const goto_modelt &);
};

#endif
