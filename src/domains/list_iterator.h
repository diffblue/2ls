/*******************************************************************\

Module: List iterator - abstraction for iterative access to a linked
                        list.

Author: Viktor Malik

\*******************************************************************/

/// \file
/// List iterator - abstraction for iterative access to a linked list.

#ifndef CPROVER_2LS_DOMAINS_LIST_ITERATOR_H
#define CPROVER_2LS_DOMAINS_LIST_ITERATOR_H

#include <limits>
#include <util/std_expr.h>
#include <set>

class list_iteratort
{
public:
  // No location (used for input variables)
  static const unsigned IN_LOC=std::numeric_limits<unsigned>::max();

  /*******************************************************************\
   Access to an object from a list iterator.
   Contains:
     - sequence of fields that are used to access the object from the
       iterator
     - location:
         IN_LOC for read access
         location number for write access
  \*******************************************************************/
  class accesst
  {
  public:
    std::vector<irep_idt> fields;
    unsigned location;

    equal_exprt binding(
      const symbol_exprt &lhs,
      const symbol_exprt &rhs,
      const unsigned level,
      const namespacet &ns) const;
  };

  // Pointer variable used to iterate the list (induction pointer)
  symbol_exprt pointer;
  // Initial value of the induction pointer (before the first iteration)
  exprt init_pointer;
  // Set of fields through which a step is done after each iteration
  std::vector<irep_idt> fields;
  mutable std::list<accesst> accesses;

  list_iteratort(
    const symbol_exprt &pointer,
    const exprt &init_pointer,
    const std::vector<irep_idt> &fields):
    pointer(pointer), init_pointer(init_pointer), fields(fields) {}

  bool operator<(const list_iteratort &rhs) const
  {
    return std::tie(pointer, fields)<std::tie(rhs.pointer, rhs.fields);
  }

  void add_access(const member_exprt &expr, unsigned location_number) const;

  const symbol_exprt access_symbol_expr(
    const accesst &access,
    unsigned level,
    const namespacet &ns) const;

  const symbol_exprt iterator_symbol() const;
};

const symbol_exprt recursive_member_symbol(
  const symbol_exprt &object,
  const irep_idt &field,
  const unsigned loc_num,
  const namespacet &ns);

#endif // CPROVER_2LS_DOMAINS_LIST_ITERATOR_H
