/*******************************************************************\

Module: Canonize addresses of objects

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Canonize addresses of objects

#include <util/c_types.h>

#include <util/std_expr.h>
#include <util/pointer_offset_size.h>

#include "address_canonizer.h"
#include "ssa_pointed_objects.h"

exprt address_canonizer(
  const exprt &address,
  const namespacet &ns)
{
  assert(ns.follow(address.type()).id()==ID_pointer);

  if(address.id()==ID_address_of)
  {
    const address_of_exprt &address_of_expr=
      to_address_of_expr(address);
    const exprt &object=address_of_expr.object();

    if(object.id()==ID_dereference)
    {
      // &*x ---> x
      return to_dereference_expr(object).pointer();
    }
    else if(object.id()==ID_member)
    {
      // get offset
      exprt offset=member_offset_expr(to_member_expr(object), ns);

      // &x.m  ---> (&x)+offset

      address_of_exprt address_of_expr(to_member_expr(object).struct_op());
      exprt rec_result=address_canonizer(address_of_expr, ns); // rec. call

      pointer_typet byte_pointer(unsigned_char_type());
      typecast_exprt typecast_expr(rec_result, byte_pointer);
      plus_exprt sum(typecast_expr, offset);
      if(sum.type()!=address.type())
        sum.make_typecast(address.type());

      return sum;
    }
    else if(object.id()==ID_index)
    {
      // &(x[i]) ---> (&x)+i
      address_of_exprt address_of_expr(to_index_expr(object).array());
      exprt rec_result=address_canonizer(address_of_expr, ns); // rec. call

      pointer_typet pointer_type;
      pointer_type.subtype()=object.type();
      typecast_exprt typecast_expr(rec_result, pointer_type);
      plus_exprt sum(typecast_expr, to_index_expr(object).index());
      if(sum.type()!=address.type())
        sum.make_typecast(address.type());

      return sum;
    }
    else
      return address;
  }
  else if(address.id()==ID_plus ||
          address.id()==ID_minus)
  {
    // one of the operands needs to be a pointer
    assert(address.operands().size()==2);
    exprt tmp=address;
    if(ns.follow(tmp.op0().type()).id()==ID_pointer)
    {
      tmp.op0()=address_canonizer(tmp.op0(), ns);
      return tmp;
    }
    else if(ns.follow(tmp.op1().type()).id()==ID_pointer)
    {
      tmp.op1()=address_canonizer(tmp.op1(), ns);
      return tmp;
    }
    else
      return tmp;
  }
  else if(address.id()==ID_if)
  {
    if_exprt tmp=to_if_expr(address);
    tmp.true_case()=address_canonizer(tmp.true_case(), ns);
    tmp.false_case()=address_canonizer(tmp.false_case(), ns);
    return tmp;
  }
  else if(address.id()==ID_typecast)
  {
    typecast_exprt tmp=to_typecast_expr(address);

    // cast from another pointer?
    if(tmp.op().type().id()==ID_pointer)
    {
      tmp.op()=address_canonizer(tmp.op(), ns);
      return tmp;
    }

    return address;
  }
  else
    return address;
}
