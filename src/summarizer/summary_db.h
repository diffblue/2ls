/*******************************************************************\

Module: Abstract Interface for a Function Summary

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SUMMARIZER_FUNCTION_SUMMARY_H
#define CPROVER_SUMMARIZER_FUNCTION_SUMMARY_H

#include "function_summary.h"

class summary_dbt
{
public:
  // retrieve a summary for function with given identifier
  const function_summaryt & operator() (const irep_idt &);
};

#endif
