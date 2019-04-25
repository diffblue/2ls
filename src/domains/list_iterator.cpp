/*******************************************************************\

Module: List iterator - abstraction for iterative access to a linked
                        list.

Author: Viktor Malik

\*******************************************************************/

/// \file
/// List iterator - abstraction for iterative access to a linked list.

#include <algorithm>
#include <ssa/ssa_pointed_objects.h>
#include "list_iterator.h"

/// Add new access to the iterator corresponding to an expression from SSA.
void list_iteratort::add_access(
  const member_exprt &expr,
  unsigned location_number) const
{
  assert(
    expr.compound().get_bool(ID_iterator) &&
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

/// \param access: Iterator access
/// \param level: Level of access (number of fields from the access to be
///   followed)
/// \param ns: Namespace
/// \return Corresponding SSA symbol.
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

/// \return SSA symbol corresponding to the iterator.
const symbol_exprt list_iteratort::iterator_symbol() const
{
  std::size_t pos=id2string(pointer.get_identifier()).find_last_of('#');
  symbol_exprt iterator(
    id2string(pointer.get_identifier()).substr(0, pos)+"'it",
    pointer.type().subtype());
  iterator.set(ID_iterator, true);

  return iterator;
}

/// \param object: Dynamic object
/// \param field: Field (must be a pointer to the type of the object)
/// \param loc_num: Location number
/// \param ns: Namespace
/// \return SSA symbol 'object.field#loc_num'
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

/// \return Binding between members of lhs and rhs given by field of specified
///   level.
equal_exprt list_iteratort::accesst::binding(
  const symbol_exprt &lhs,
  const symbol_exprt &rhs,
  const unsigned level,
  const namespacet &ns) const
{
  unsigned loc=level==fields.size()-1 ? location : IN_LOC;
  const symbol_exprt lhs_sym=
    recursive_member_symbol(lhs, fields.at(level), loc, ns);
  const symbol_exprt rhs_sym=
    recursive_member_symbol(rhs, fields.at(level), loc, ns);
  return equal_exprt(lhs_sym, rhs_sym);
}
