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

  struct block_call_infot 
  {
    irep_idt identifier;
    locationt location;
    unsigned unwind;
    varst arguments;
    exprt guard_call;
    varst returns;
    exprt guard_return;
    exprt cond_term;
  };
  typedef std::vector<block_call_infot> block_callst;  
  typedef std::vector<exprt> assertionst;  

  //block interface
  irep_idt identifier;
  varst inputs;
  exprt guard_in;
  varst outputs;
  exprt guard_out;
//  exprt body;
  block_callst block_calls;
//  assertionst assertions;

protected:
};

#endif
