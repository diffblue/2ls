/**
 *  Viktor Malik, 2/6/17 (c).
 */
#ifndef CPROVER_LIST_ITERATOR_H
#define CPROVER_LIST_ITERATOR_H


#include <util/std_expr.h>
#include <set>

class list_iteratort
{
 public:
  static const int IN_LOC = -1;

  class accesst
  {
   public:
    std::vector<irep_idt> fields;
    int location;

    equal_exprt binding(const symbol_exprt &lhs, const symbol_exprt &rhs,
                            const unsigned level, const namespacet &ns) const;
  };

  symbol_exprt pointer;
  exprt init_pointer;
  std::vector<irep_idt> fields;
  mutable std::list<accesst> accesses;

  list_iteratort(const symbol_exprt &pointer, const exprt &init_pointer,
                 const std::vector<irep_idt> &fields)
      : pointer(pointer), init_pointer(init_pointer), fields(fields) {}

  bool operator<(const list_iteratort &rhs) const
  {
    return std::tie(pointer, fields) < std::tie(rhs.pointer, rhs.fields);
  }

  void add_access(const member_exprt &expr, int location_number) const;

  const symbol_exprt
  access_symbol_expr(const accesst &access, unsigned level, const namespacet &ns) const;

  const symbol_exprt iterator_symbol() const;
};

const symbol_exprt recursive_member_symbol(const symbol_exprt &object, const irep_idt &member, const int loc_num,
                                           const namespacet &ns);

#endif //CPROVER_LIST_ITERATOR_H
