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
  identifier=goto_function.body.instructions.begin()->function;
  guard_in=guard_symbol(goto_function.body.instructions.begin());
  inputs=params;
  inputs.insert(inputs.end(),globals_in.begin(),globals_in.end());
  guard_out=guard_symbol(--goto_function.body.instructions.end());
  outputs.insert(outputs.end(),globals_out.begin(),globals_out.end());
  for(const auto &n : nodes)
  {
    if(n.empty()) 
      continue;
    for(const auto &f : n.function_calls)
    {
      block_calls.push_back(block_call_infot());
      block_call_infot &bc=block_calls.back();
      bc.identifier=to_symbol_expr(f.function()).get_identifier();
      bc.location=n.location;
      bc.unwind=0;
      for(const auto &e : f.arguments())
        bc.arguments.push_back(to_symbol_expr(e));
      //TODO: find a better solution for that
      std::set<symbol_exprt> cs_globals_in, cs_globals_out;
      get_cs_globals(n.location, bc.identifier, cs_globals_in, cs_globals_out);
      bc.arguments.insert(bc.arguments.end(),
                          cs_globals_in.begin(), cs_globals_in.end());
      bc.guard_call=guard_symbol(n.location);
      bc.returns.insert(bc.returns.end(),
                        cs_globals_out.begin(), cs_globals_out.end());
      goto_programt::const_targett next=n.location; ++next;
      assert(next!=goto_function.body.instructions.end());
      bc.guard_return=guard_symbol(next);
      bc.cond_term=cond_symbol(n.location);
    }
  }
}
