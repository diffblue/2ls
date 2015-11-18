/*******************************************************************\

Module: ACDL Solver

Author: Rajdeep Mukherjee

\*******************************************************************/

#ifndef CPROVER_ACDL_SOLVER_H
#define CPROVER_ACDL_SOLVER_H

#include <util/options.h>
#include <goto-programs/property_checker.h>
#include "acdl_domain.h"

#include "../ssa/local_ssa.h"

class acdl_solvert : public messaget
{
public:

  //typedef std::list<exprt> worklist;
  //typedef exprt valuet;
  explicit acdl_solvert(const optionst &_options,
    acdl_domaint &_domain)
    : 
    options(_options),
    domain(_domain)
    {
    }  

  ~acdl_solvert() 
    {
    }

  property_checkert::resultt operator()(const local_SSAt &SSA);

protected:
  const optionst &options;
  acdl_domaint &domain;
};


#endif
 
