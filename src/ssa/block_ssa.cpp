/*******************************************************************\

Module: Block SSA

Author: Peter Schrammel

\*******************************************************************/

#include "block_ssa.h"

/*******************************************************************\

Function: block_ssat::block_ssat

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

block_ssat::block_ssat(
  const goto_functiont &_goto_function,
  const namespacet &_ns,
  const std::string &_suffix)
  :
  unwindable_local_SSAt(_goto_function,_ns,_suffix)
{
  //TODO: initialise
}
