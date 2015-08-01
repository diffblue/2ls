/*******************************************************************\

Module: Aliasing Decision

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SSA_ALIASING_H
#define CPROVER_SSA_ALIASING_H

#include <util/std_expr.h>
#include <util/namespace.h>

#include "ssa_value_set.h"

//bool ssa_may_alias(const exprt &, const exprt &, const namespacet &);
//exprt ssa_alias_guard(const exprt &, const exprt &, const namespacet &);
//exprt ssa_alias_value(const exprt &, const exprt &, const namespacet &);

exprt dereference(
  const exprt &,
  const ssa_value_domaint &,
  const std::string &nondet_prefix,
  const namespacet &);

#endif
