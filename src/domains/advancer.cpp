/**
 *  Viktor Malik, 2/6/17 (c).
 */

#include "advancer.h"

const symbol_exprt advancert::symbol_expr() const
{
  return symbol_exprt(id2string(input_pointer_id()) + "'obj." + id2string(member) + "'adv",
                      pointer.type().subtype());
}

const symbol_exprt advancert::instance_symbol_expr(const irep_idt &member,
                                                   const int location_number) const
{
  return recursive_member_symbol(symbol_expr(), member, location_number);
}

const std::list<std::pair<irep_idt, int>> advancert::output_instances() const
{
  std::list<std::pair<irep_idt, int>> result;

  // Find instance with maximal location number
  for (auto &instance : instances)
  {
    int max_loc = *(--(instance.second.end()));
    if (max_loc >= 0)
      result.emplace_back(instance.first, max_loc);
  }

  return result;
}

const symbol_exprt advancert::input_pointer() const
{
  return symbol_exprt(input_pointer_id(), pointer.type());
}

const irep_idt advancert::input_pointer_id() const
{
  const irep_idt id = pointer.get_identifier();
  return id2string(id).substr(0, id2string(id).rfind("#"));
}

const symbol_exprt recursive_member_symbol(const symbol_exprt &object,
                                           const irep_idt &member,
                                           const int loc_num)
{
  std::string suffix = loc_num != advancert::IN_LOC ? ("#" + std::to_string(loc_num)) : "";
  return symbol_exprt(id2string(object.get_identifier()) + "." + id2string(member) + suffix,
                      pointer_typet(object.type()));
}
