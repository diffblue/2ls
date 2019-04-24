/*******************************************************************\

Module: Symbolic path in a program

Author: Viktor Malik

\*******************************************************************/


/// \file
/// Symbolic path in a program

#include "symbolic_path.h"

/// Get expression correcponding to the path. There is an option not to include
/// selected loop guard (this is useful when analysing that loop).
const exprt symbolic_patht::get_expr(
  const exprt &except_guard,
  bool except_true_only) const
{
  exprt::operandst path;
  for(const auto &guard : path_map)
  {
    if(except_guard.is_not_nil() && guard.first==except_guard &&
       (!except_true_only || guard.second))
      continue;

    if(guard.second)
      path.push_back(guard.first);
    else
      path.push_back(not_exprt(guard.first));
  }
  return path.empty() ? true_exprt() : conjunction(path);
}
