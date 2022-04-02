/*******************************************************************\
Module: SSA Unwinder
Author: František Nečas
\*******************************************************************/

/// \file
/// SSA Unwinder

#include "simplify_ssa.h"
#include "goto_unwinder.h"

void goto_local_unwindert::unwind(unsigned int k)
{
}

/// No-op, no special initialization is necessary in this unwinder.
void goto_local_unwindert::init()
{
}

/// No-op, the continuation of loops is not special in any way in this unwinder,
/// the code using this method collects the guard and condition of the loop
/// on its own.
void goto_local_unwindert::loop_continuation_conditions(
  exprt::operandst &loop_cont) const
{
}

/// No-op, since we recompute the SSA every time, the indices of SSA nodes
/// change and the naming scheme from ssa_unwindert is not applicable.
/// The lack of support for this makes nontermination not work with this
/// unwinder.
void goto_local_unwindert::unwinder_rename(
  symbol_exprt &var,
  const local_SSAt::nodet &node,
  bool pre) const
{
}

void goto_unwindert::unwind_all(unsigned int k)
{
  assert(is_initialized);

  for (auto &local_unwinder : unwinder_map)
    local_unwinder.second.unwind(k);
}

void goto_unwindert::init(unwinder_modet mode)
{
  for(auto &f : ssa_db.functions())
  {
    unwinder_map.insert(
      {
        f.first,
        goto_local_unwindert(
          ssa_db,
          goto_model.goto_functions.function_map.at(f.first),
          mode,
          simplify)});
  }
}

void goto_unwindert::init_localunwinders()
{
  for(auto &local_unwinder : unwinder_map)
    local_unwinder.second.init();
  is_initialized=true;
}