/*******************************************************************\

Module: Translate Union Members into Typecast

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_TRANSLATE_UNION_MEMBER_H
#define CPROVER_TRANSLATE_UNION_MEMBER_H

#include <util/std_expr.h>
#include <util/namespace.h>

void translate_union_member(exprt &, const namespacet &);

#endif
