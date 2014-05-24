/*******************************************************************\

Module: Aliasing Decision

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SSA_ALIASING_H
#define CPROVER_SSA_ALIASING_H

#include <util/std_expr.h>
#include <util/namespace.h>

bool may_alias(const exprt &, const exprt &, const namespacet &);
exprt alias_guard(const dereference_exprt &, const exprt &, const namespacet &);
exprt alias_value(const dereference_exprt &, const exprt &, const namespacet &);

#endif
