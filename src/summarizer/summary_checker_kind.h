/*******************************************************************\

Module: Summary Checker for k-induction

Author: Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_SUMMARY_CHECKER_KIND_H
#define CPROVER_SUMMARY_CHECKER_KIND_H

#include "summary_checker_base.h"

class summary_checker_kindt:public summary_checker_baset
{
public:
  inline summary_checker_kindt(optionst &_options):
    summary_checker_baset(_options)
  {
  }
  
  virtual resultt operator()(const goto_modelt &);

};

#endif
