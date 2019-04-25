/*******************************************************************\

Module: Translate Union Members into Typecast

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Translate Union Members into Typecast

#include "translate_union_member.h"

/// Turns union.member into *((T *)(&union)), where T is the type of the member.
/// This is semantics-preserving for unions, but requires some elaboration in
/// case the union member is an array.
void translate_union_member(exprt &dest, const namespacet &ns)
{
#if 0
  if(dest.id()==ID_member)
  {
    // TODO
  }

  address_of_exprt address_of_expr(member_expr.struct_op());
  pointer_typet pointer_type(member_expr.type());
  typecast_exprt typecast_expr(address_of_expr, pointer_type);
  return dereference_exprt(typecast_expr, member_expr.type());
#endif
}
