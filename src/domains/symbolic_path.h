/*******************************************************************\

Module: Symbolic path in a program

Author: Viktor Malik

\*******************************************************************/

/// \file
/// Symbolic path in a program

#ifndef CPROVER_2LS_DOMAINS_SYMBOLIC_PATH_H
#define CPROVER_2LS_DOMAINS_SYMBOLIC_PATH_H

#include <util/expr.h>
#include <util/std_expr.h>

class symbolic_patht
{
public:
  std::map<exprt, bool> path_map;

  const exprt get_expr(
    const exprt &except_guard=nil_exprt(),
    bool except_true_only=false) const;

  bool &operator[](const exprt &expr) { return path_map[expr]; }

  void clear() { path_map.clear(); }
};


#endif // CPROVER_2LS_DOMAINS_SYMBOLIC_PATH_H
