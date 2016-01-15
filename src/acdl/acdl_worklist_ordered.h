/*******************************************************************\

Module: ACDL Decision Heuristics (Branch on Condition Variables)

Author: Rajdeep Mukherjee, Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_ACDL_WORKLIST_ORDERED_H
#define CPROVER_ACDL_WORKLIST_ORDERED_H

#include "acdl_worklist_base.h"

class acdl_worklist_orderedt : public acdl_worklist_baset
{
public:
  explicit acdl_worklist_orderedt()
    : 
  acdl_worklist_baset()
  {
  }
  
  virtual void initialize(const local_SSAt &SSA);

protected:
  void push_into_assertion_list (assert_listt &aexpr,
				 const acdl_domaint::statementt &statement);


};

#endif
