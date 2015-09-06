/*******************************************************************\

Module: Summary Checker for AI

Author: Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_SUMMARY_CHECKER_AI_H
#define CPROVER_SUMMARY_CHECKER_AI_H

#include "summary_checker_base.h"

class summary_checker_ait:public summary_checker_baset
{
public:
  inline summary_checker_ait(optionst &_options):
    summary_checker_baset(_options)
  {
  }
  
  virtual resultt operator()(const goto_modelt &);

protected:
  void report_preconditions();

};

#endif
