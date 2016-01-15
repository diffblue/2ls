/*******************************************************************\

Module: ACDL Initialization Heuristics Interface

Author: Rajdeep Mukherjee, Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_ACDL_INITIALIZE_HEURISTICS_H
#define CPROVER_ACDL_INITIALIZE_HEURISTICS_H

#include <goto-programs/property_checker.h>

#include "acdl_domain.h"
#include "../ssa/local_ssa.h"

class acdl_worklist_initializet : public messaget
{
public:
  
  //override this
  virtual void operator()(
    const local_SSAt &SSA,
    worklistt &worklist)
  {
    assert(false);
  }

protected:
  acdl_domaint &domain;
  
  explicit acdl_worklist_initializet(
    acdl_domaint &_domain)
    : 
  domain(_domain)
  {
  }  

  ~acdl_worklist_initializet() 
  {
  }
};

#endif
