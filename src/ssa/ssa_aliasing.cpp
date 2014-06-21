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
#include <util/suffix.h>
#include <util/cprover_prefix.h>
#include <util/std_expr.h>
#include <util/pointer_predicates.h>
#include <util/pointer_offset_size.h>
#include <util/arith_tools.h>
#include <util/byte_operators.h>

#include <ansi-c/c_types.h>

#include "ssa_aliasing.h"
#include "address_canonizer.h"

/*******************************************************************\

Function: ssa_may_alias

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool ssa_may_alias(
  const exprt &e1,
  const exprt &e2,
  const namespacet &ns)
{
  #ifdef DEBUG
  std::cout << "MAY ALIAS1 " << from_expr(ns, "", e1) << " "
                             << from_expr(ns, "", e2) << "\n";
  #endif

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
    
  // __CPROVER symbols
  if(e1.id()==ID_symbol &&
     has_prefix(id2string(to_symbol_expr(e1).get_identifier()), CPROVER_PREFIX))
    return false;

  if(e2.id()==ID_symbol &&
     has_prefix(id2string(to_symbol_expr(e2).get_identifier()), CPROVER_PREFIX))
    return false;

  if(e1.id()==ID_symbol &&
     has_suffix(id2string(to_symbol_expr(e1).get_identifier()), "#return_value"))
    return false;

  if(e2.id()==ID_symbol &&
     has_suffix(id2string(to_symbol_expr(e2).get_identifier()), "#return_value"))
    return false;

  // Both member?
  if(e1.id()==ID_member &&
     e2.id()==ID_member)
  {
    const member_exprt &m1=to_member_expr(e1);
    const member_exprt &m2=to_member_expr(e2);
    
    // same component?
    if(m1.get_component_name()!=m2.get_component_name())
      return false;
    
    return ssa_may_alias(m1.struct_op(), m2.struct_op(), ns);
  }

  // Both index?
  if(e1.id()==ID_index &&
     e2.id()==ID_index)
  {
    const index_exprt &i1=to_index_expr(e1);
    const index_exprt &i2=to_index_expr(e2);

    return ssa_may_alias(i1.array(), i2.array(), ns);
  }

  const typet &t1=ns.follow(e1.type());
  const typet &t2=ns.follow(e2.type());
  
  // Pointers only alias with other pointers, a restriction.
  if(t1.id()==ID_pointer)
    return t2.id()==ID_pointer;
  
  if(t2.id()==ID_pointer)
    return t1.id()==ID_pointer;
  
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
    {
      return true;
    }
      
    // should consider further options, e.g., struct prefixes      
    return false;
  }

  return false; // both different objects
}

/*******************************************************************\

Function: ssa_alias_guard

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt ssa_alias_guard(
  const exprt &e1,
  const exprt &e2,
  const namespacet &ns)
{
  exprt a1=address_canonizer(address_of_exprt(e1), ns);
  exprt a2=address_canonizer(address_of_exprt(e2), ns);
  
  // in some cases, we can use plain address equality,
  // as we assume well-aligned-ness
  mp_integer size1=pointer_offset_size(ns, e1.type());
  mp_integer size2=pointer_offset_size(ns, e2.type());
  
  if(size1>=size2)
  {
    exprt lhs=a1;
    exprt rhs=a2;
    if(ns.follow(rhs.type())!=ns.follow(lhs.type()))
      rhs=typecast_exprt(rhs, lhs.type());
  
    return equal_exprt(lhs, rhs);
  }
  
  return same_object(a1, a2);
}

/*******************************************************************\

Function: ssa_alias_value

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt ssa_alias_value(
  const exprt &e1,
  const exprt &e2,
  const namespacet &ns)
{
  const typet &e1_type=ns.follow(e1.type());
  const typet &e2_type=ns.follow(e2.type());

  // type matches?
  if(e1_type==e2_type)
    return e2;

  exprt a1=address_canonizer(address_of_exprt(e1), ns);
  exprt a2=address_canonizer(address_of_exprt(e2), ns);
  
  exprt offset1=pointer_offset(a1);

  // array index possible?
  if(e2_type.id()==ID_array &&
     e1_type==ns.follow(e2_type.subtype()))
  {
    // this assumes well-alignedness

    mp_integer element_size=pointer_offset_size(ns, e2_type.subtype());

    if(element_size==1)
      return index_exprt(e2, offset1, e1.type());
    else if(element_size>1)
    {
      exprt index=div_exprt(offset1, from_integer(element_size, offset1.type()));
      return index_exprt(e2, index, e1.type());
    }
  }

  byte_extract_exprt byte_extract(byte_extract_id(), e1.type());
  byte_extract.op()=e2;
  byte_extract.offset()=offset1;
  
  return byte_extract; 
}
