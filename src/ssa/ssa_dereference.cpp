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
#include <util/base_type.h>
#include <util/expr_util.h>
#include <util/simplify_expr.h>

#include <ansi-c/c_types.h>

#include "ssa_dereference.h"
#include "address_canonizer.h"

/*******************************************************************\

Function: lift_if

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt lift_if(const exprt &src)
{
  if(src.operands().size()==1 && src.op0().id()==ID_if)
  {
    // push operator into ?:
    if_exprt if_expr=to_if_expr(src.op0());
    if_expr.type()=src.type();

    if(if_expr.true_case().is_not_nil())
    {
      exprt previous=if_expr.true_case();
      if_expr.true_case()=src;
      if_expr.true_case().op0()=previous;
    }
      
    if(if_expr.false_case().is_not_nil())
    {
      exprt previous=if_expr.false_case();
      if_expr.false_case()=src;
      if_expr.false_case().op0()=previous;
    }

    return if_expr;
  }
  else
    return src;
}

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
    return to_symbol_expr(e1).get_identifier()==
           to_symbol_expr(e2).get_identifier();
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
  
  // If one is an array and the other not, consider the elements
  if(t1.id()==ID_array && t2.id()!=ID_array)
    if(ssa_may_alias(index_exprt(e1, gen_zero(index_type()), t1.subtype()), e2, ns))
      return true;
  
  if(t2.id()==ID_array && t2.id()!=ID_array)
    if(ssa_may_alias(e1, index_exprt(e2, gen_zero(index_type()), t2.subtype()), ns))
      return true;
  
  // Pointers only alias with other pointers,
  // which is a restriction.
  if(t1.id()==ID_pointer)
    return t2.id()==ID_pointer;
  
  if(t2.id()==ID_pointer)
    return t1.id()==ID_pointer;
  
  // Is one a scalar pointer?
  if(e1.id()==ID_dereference &&
     (t1.id()==ID_signedbv || t1.id()==ID_unsignedbv || t1.id()==ID_floatbv))
    return true;
  
  if(e2.id()==ID_dereference &&
     (t2.id()==ID_signedbv || t2.id()==ID_unsignedbv || t1.id()==ID_floatbv))
    return true;
  
  // Is one a pointer?
  if(e1.id()==ID_dereference ||
     e2.id()==ID_dereference)
  {
    // look at the types

    // same type?
    if(base_type_eq(t1, t2, ns))
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
  //TODO: We should compare 'base' pointers here because
  // we have a higher chance that there was no pointer arithmetic
  // on the base pointer than that the result of the pointer
  // arithmetic points to a base pointer.
  // The following hack does that:
  if(a1.id()==ID_plus) a1 = a1.op0();
  
  exprt a2=address_canonizer(address_of_exprt(e2), ns);
  
  // in some cases, we can use plain address equality,
  // as we assume well-aligned-ness
  mp_integer size1=pointer_offset_size(e1.type(), ns);
  mp_integer size2=pointer_offset_size(e2.type(), ns);
  
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

    mp_integer element_size=pointer_offset_size(e2_type.subtype(), ns);

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

/*******************************************************************\

Function: dereference_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt dereference_rec(
 const exprt &src,
 const ssa_value_domaint &ssa_value_domain, 
 const std::string &nondet_prefix,
 const namespacet &ns)
{
  if(src.id()==ID_dereference)
  {
    const exprt &pointer=to_dereference_expr(src).pointer();
    exprt pointer_deref=dereference(pointer, ssa_value_domain, nondet_prefix, ns);

    // We use the identifier produced by
    // local_SSAt::replace_side_effects_rec
    exprt result=symbol_exprt(nondet_prefix, src.type());

    // query the value sets
    const ssa_value_domaint::valuest values=
      ssa_value_domain(pointer, ns);

    for(ssa_value_domaint::valuest::value_sett::const_iterator
        it=values.value_set.begin();
        it!=values.value_set.end();
        it++)
    {
      exprt guard=ssa_alias_guard(src, it->get_expr(), ns);
      exprt value=ssa_alias_value(src, it->get_expr(), ns);
      result=if_exprt(guard, value, result);
    }

    return result;
  }
  else if(src.id()==ID_member)
  {
    member_exprt tmp=to_member_expr(src);
    tmp.struct_op()=dereference_rec(tmp.struct_op(), ssa_value_domain, nondet_prefix, ns);
    
    #ifdef DEBUG
    std::cout << "dereference_rec tmp: " << from_expr(ns, "", tmp) << '\n';
    #endif

    if(tmp.struct_op().is_nil())
      return nil_exprt();
      
    return lift_if(tmp);
  }
  else if(src.id()==ID_address_of)
  {
    address_of_exprt tmp=to_address_of_expr(src);
    tmp.object()=dereference_rec(tmp.object(), ssa_value_domain, nondet_prefix, ns);

    if(tmp.object().is_nil())
      return nil_exprt();
    
    return lift_if(tmp);
  }
  else
  {
    exprt tmp=src;
    Forall_operands(it, tmp)
      *it=dereference_rec(*it, ssa_value_domain, nondet_prefix, ns);
    return tmp;
  }
}

/*******************************************************************\

Function: dereference

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt dereference(
 const exprt &src,
 const ssa_value_domaint &ssa_value_domain, 
 const std::string &nondet_prefix,
 const namespacet &ns)
{
  #ifdef DEBUG
  std::cout << "dereference src: " << from_expr(ns, "", src) << '\n';
  #endif

  exprt tmp1=dereference_rec(src, ssa_value_domain, nondet_prefix, ns);

  #ifdef DEBUG
  std::cout << "dereference tmp1: " << from_expr(ns, "", tmp1) << '\n';
  #endif

  exprt tmp2=simplify_expr(tmp1, ns);

  #ifdef DEBUG
  std::cout << "dereference tmp2: " << from_expr(ns, "", tmp2) << '\n';
  #endif

  return tmp2;
}
