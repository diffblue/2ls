/*******************************************************************\

Module: Translate Union Members into Typecast

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Translate Union Members into Typecast

#ifndef CPROVER_2LS_SSA_TRANSLATE_UNION_MEMBER_H
#define CPROVER_2LS_SSA_TRANSLATE_UNION_MEMBER_H

#include <util/std_expr.h>
#include <util/namespace.h>

void translate_union_member(exprt &, const namespacet &);

#endif
