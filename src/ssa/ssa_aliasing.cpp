/*******************************************************************\

Module: Aliasing Decision

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

//#define DEBUG

#ifdef DEBUG
#include <iostream>
#include <langapi/language_util.h>
#endif

#include <util/prefix.h>
#include <util/cprover_prefix.h>
#include <util/std_expr.h>
#include <util/pointer_predicates.h>

#include <ansi-c/c_types.h>

#include "ssa_aliasing.h"

/*******************************************************************\

Function: may_alias

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool may_alias(
  const exprt &e1,
  const exprt &e2,
  const namespacet &ns)
{
  #ifdef DEBUG
  std::cout << "MAY ALIAS1 " << from_expr(ns, "", e1) << " "
                             << from_expr(ns, "", e2) << "\n";
  #endif

  // __CPROVER symbols
  if(e1.id()==ID_symbol &&
     has_prefix(id2string(to_symbol_expr(e1).get_identifier()), CPROVER_PREFIX))
    return false;

  if(e2.id()==ID_symbol &&
     has_prefix(id2string(to_symbol_expr(e2).get_identifier()), CPROVER_PREFIX))
    return false;

  // The same?
  if(e1==e2)
    return true;

  // Both symbol?
  if(e1.id()==ID_symbol &&
     e2.id()==ID_symbol)
  {
    // not the same, so different
    return false;
  }
    
  // Both member?
  if(e1.id()==ID_member &&
     e2.id()==ID_member)
  {
    const member_exprt &m1=to_member_expr(e1);
    const member_exprt &m2=to_member_expr(e2);
    
    // same component?
    if(m1.get_component_name()!=m2.get_component_name())
      return false;
    
    return may_alias(m1.struct_op(), m2.struct_op(), ns);
  }

  // Both index?
  if(e1.id()==ID_index &&
     e2.id()==ID_index)
  {
    const index_exprt &i1=to_index_expr(e1);
    const index_exprt &i2=to_index_expr(e2);

    return may_alias(i1.array(), i2.array(), ns);
  }

  const typet &t1=ns.follow(e1.type());
  const typet &t2=ns.follow(e2.type());
  
  // Is one a scalar pointer?
  if(e1.id()==ID_dereference &&
     (t1.id()==ID_signedbv || t1.id()==ID_unsignedbv))
    return true;
  
  if(e2.id()==ID_dereference &&
     (t2.id()==ID_signedbv || t2.id()==ID_unsignedbv))
    return true;
  
  // Is one a pointer?
  if(e1.id()==ID_dereference ||
     e2.id()==ID_dereference)
  {
    // look at the types

    // same type?
    if(t1==t2)
      return true;
      
    // should consider further options, e.g., struct prefixes      
    return false;
  }

  return false; // both different objects
}

/*******************************************************************\

Function: alias_guard

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt alias_guard(
  const dereference_exprt &e1,
  const exprt &e2,
  const namespacet &ns)
{
  const typet &e2_type=ns.follow(e2.type());

  exprt e2_address=address_of_exprt(e2);

  // is e2 an array, struct, or union?
  if(e2_type.id()==ID_array ||
     e2_type.id()==ID_struct ||
     e2_type.id()==ID_union)
  {
    return same_object(e1.pointer(), e2_address);
  }

  // in some cases, we can use plain equality
  exprt lhs=e1.pointer();
  exprt rhs=e2_address;
  if(ns.follow(rhs.type())!=ns.follow(lhs.type()))
    rhs=typecast_exprt(rhs, lhs.type());
  
  return equal_exprt(lhs, rhs);
}

/*******************************************************************\

Function: alias_value

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt alias_value(
  const dereference_exprt &e1,
  const exprt &e2,
  const namespacet &ns)
{
  const typet &e1_type=ns.follow(e1.type());
  const typet &e2_type=ns.follow(e2.type());

  // type matches?
  if(e1_type==e2_type)
    return e2;

  unary_exprt offset(ID_pointer_offset, e1.pointer(), size_type());

  binary_exprt byte_extract(ID_byte_extract_little_endian, e1.type());
  byte_extract.op0()=e2;
  byte_extract.op1()=offset;
  
  return byte_extract; 
}
