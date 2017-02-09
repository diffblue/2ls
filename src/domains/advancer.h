/**
 *  Viktor Malik, 2/6/17 (c).
 */
#ifndef INC_2LS_ADVANCERT_H
#define INC_2LS_ADVANCERT_H


#include <util/std_expr.h>
#include <set>

class advancert
{
 public:
  static const int IN_LOC = -1;

  symbol_exprt pointer;
  irep_idt member;

  mutable std::map<irep_idt, std::set<int> > instances;

  advancert(const symbol_exprt &pointer_, const irep_idt &member_)
      : pointer(pointer_), member(member_) {}

  bool operator<(const advancert &rhs) const
  {
    return std::tie(pointer, member) < std::tie(rhs.pointer, rhs.member);
  }

  void add_instance(const irep_idt &member, const int location_number) const
  {
    instances[member].insert(location_number);
  }

  const symbol_exprt input_pointer() const;

  const symbol_exprt symbol_expr() const;

  const symbol_exprt instance_symbol_expr(const irep_idt &member, const int location_number) const;

  const std::list<std::pair<irep_idt, int>> output_instances() const;

 protected:
  const irep_idt input_pointer_id() const;
};


const symbol_exprt recursive_member_symbol(const symbol_exprt &object,
                                           const irep_idt &member,
                                           const int loc_num);


#endif //INC_2LS_ADVANCERT_H
