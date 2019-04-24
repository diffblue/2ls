/*******************************************************************\

Module: Aliasing Decision

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Aliasing Decision

#ifndef CPROVER_2LS_SSA_SSA_DEREFERENCE_H
#define CPROVER_2LS_SSA_SSA_DEREFERENCE_H

#include <util/std_expr.h>
#include <util/namespace.h>

#include "ssa_value_set.h"

exprt dereference(
  const exprt &,
  const ssa_value_domaint &,
  const std::string &nondet_prefix,
  const namespacet &);

#endif
