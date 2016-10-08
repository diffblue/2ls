/*******************************************************************\

Module: Block SSA

Author: Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_2LS_BLOCK_SSA_H
#define CPROVER_2LS_BLOCK_SSA_H

#include "unwindable_local_ssa.h"

class block_ssat : public unwindable_local_SSAt
{
public:
  block_ssat(
    const goto_functiont &_goto_function,
    const namespacet &_ns,
    const std::string &_suffix="");

  virtual ~block_ssat() {}

  typedef std::vector<symbol_exprt> varst;

  varst inputs;
  varst outputs;
  exprt body;

  struct function_call_infot 
  {
    irep_idt name;
    locationt location;
    unsigned unwind;
    varst inputs;
    varst outputs;
  };
  typedef std::vector<function_call_infot> function_callst;  
  function_callst function_calls;
 
  typedef std::vector<exprt> assertionst;  
  assertionst assertions;

protected:
};

#endif
