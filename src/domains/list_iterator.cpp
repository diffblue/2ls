/*******************************************************************\

Module: List iterator - abstraction for iterative access to a linked
                        list.

Author: Viktor Malik

\*******************************************************************/

#include <algorithm>
#include <ssa/ssa_pointed_objects.h>
#include "list_iterator.h"

/*******************************************************************\

Function: list_iteratort::add_access

  Inputs:

 Outputs:

 Purpose: Add new access to the iterator corresponding to
          an expression from SSA.

\*******************************************************************/

void list_iteratort::add_access(
  const member_exprt &expr,
  unsigned location_number) const
{
  assert(expr.compound().get_bool(ID_iterator) &&
         expr.compound().get_bool(ID_pointed));

  accesst access;
  access.location=location_number;

  unsigned level=pointed_level(expr.compound());
  unsigned iterator_level=it_value_level(expr.compound());
  for(unsigned l=iterator_level; l<level; ++l)
  {
    access.fields.push_back(pointer_level_field(expr.compound(), l));
  }
  access.fields.push_back(expr.get_component_name());

  accesses.push_back(access);
}

/*******************************************************************\

Function: list_iteratort::access_symbol_expr

  Inputs: Iterator access
          Level of access (number of fields from the access to be followed)

 Outputs: Corresponding SSA symbol.

 Purpose:

\*******************************************************************/

const symbol_exprt list_iteratort::access_symbol_expr(
  const accesst &access,
  unsigned level,
  const namespacet &ns) const
{
  unsigned location=level==access.fields.size()-1 ? access.location : IN_LOC;
  if(level==0)
  {
    return recursive_member_symbol(
      iterator_symbol(),
      access.fields.at(level),
      location,
      ns);
  }
  else
  {
    return recursive_member_symbol(
      access_symbol_expr(access, level-1, ns),
      access.fields.at(level),
      location,
      ns);
  }
}

/*******************************************************************\

Function: list_iteratort::iterator_symbol

  Inputs:

 Outputs: SSA symbol corresponding to the iterator.

 Purpose:

\*******************************************************************/

const symbol_exprt list_iteratort::iterator_symbol() const
{
  symbol_exprt iterator(id2string(pointer.get_identifier()).substr(0, id2string(
    pointer.get_identifier()).find_last_of('#'))+"'it",
                        pointer.type().subtype());
  iterator.set(ID_iterator, true);

  return iterator;
}

/*******************************************************************\

Function: recursive_member_symbol

  Inputs: Dynamic object
          Field (must be a pointer to the type of the object)
          Location number

 Outputs: SSA symbol 'object.field#loc_num'

 Purpose:

\*******************************************************************/

const symbol_exprt recursive_member_symbol(
  const symbol_exprt &object,
  const irep_idt &field,
  const unsigned loc_num,
  const namespacet &ns)
{
  typet type=nil_typet();
  const typet &object_type=ns.follow(object.type());
  assert(object_type.id()==ID_struct);
  for(auto &component : to_struct_type(object_type).components())
  {
    if(component.get_name()==field)
      type=component.type();
  }
  assert(type.is_not_nil());

  std::string suffix=
    loc_num!=list_iteratort::IN_LOC ? ("#"+std::to_string(loc_num)) : "";
  symbol_exprt symbol(
    id2string(object.get_identifier())+"."+id2string(field)+suffix, type);
  copy_pointed_info(symbol, object);
  copy_iterator(symbol, object);

  return symbol;
}

/*******************************************************************\

Function: list_iteratort::accesst::binding

  Inputs:

 Outputs: Binding between members of lhs and rhs given by field of
          specified level.

 Purpose:

\*******************************************************************/

equal_exprt list_iteratort::accesst::binding(
  const symbol_exprt &lhs,
  const symbol_exprt &rhs,
  const unsigned level,
  const namespacet &ns) const
{
  unsigned loc=level==fields.size()-1 ? location : IN_LOC;
  return equal_exprt(
    recursive_member_symbol(lhs, fields.at(level), loc, ns),
    recursive_member_symbol(rhs, fields.at(level), loc, ns));
}
