/*******************************************************************\

Module: ACDL Decision Heuristics (Branch on Condition Variables)

Author: Rajdeep Mukherjee, Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_ACDL_WORKLIST_INITIALIZE_ORDERED_H
#define CPROVER_ACDL_WORKLIST_INITIALIZE_ORDERED_H

#include "acdl_worklist_initialize.h"

class acdl_worklist_initialize_orderedt : public acdl_worklist_initializet
{
public:
  explicit acdl_worklist_initialize_orderedt(
    acdl_domaint &_domain)
    : 
  acdl_worklist_initializet(_domain)
  {
  }
  
  virtual void operator()(
    const local_SSAt &SSA,
    worklistt &worklist);

};

#endif
