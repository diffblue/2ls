//
// Created by vmalik on 5/14/18.
//

#include <iostream>
#include "dynobj_instance_analysis.h"
#include "ssa_dereference.h"

bool has_deref_of(const exprt &expr, const exprt &pointer)
{
  if(expr.id()==ID_dereference && to_dereference_expr(expr).pointer()==pointer)
    return true;
  forall_operands(it, expr)
  {
    if(has_deref_of(*it, pointer))
      return true;
  }
  return false;
}

void remove_dereferences(const exprt &pointer, must_alias_setst &instances)
{
  for (auto &i : instances)
  {
    if (has_deref_of(i, pointer))
      instances.isolate(i);
  }
}

void replace_pointer_in_deref(exprt &deref, const exprt &src, const exprt &dest)
{
  if (deref.id() == ID_dereference && to_dereference_expr(deref).pointer() == src)
    deref = dereference_exprt(dest, deref.type());

  Forall_operands(it, deref)
    replace_pointer_in_deref(*it, src, dest);
}

void add_aliased_dereferences(const exprt &pointer, must_alias_setst &instances)
{
  for (auto &i : instances)
  {
    if(i.id()==ID_symbol && pointer.id()==ID_symbol && i!=pointer &&
       instances.same_set(i, pointer))
    {
      for (auto &deref_i : instances)
      {
        if (has_deref_of(deref_i, i))
        {
          exprt deref_copy = deref_i;
          replace_pointer_in_deref(deref_copy, i, pointer);
          instances.make_union(deref_i, deref_copy);
        }
      }
    }
  }
}

void dynobj_instance_domaint::rhs_concretisation(
  const exprt &guard,
  ai_domain_baset::locationt loc,
  ai_baset &ai,
  const namespacet &ns)
{
    forall_operands(it, guard)
    {
      if(it->id() == ID_symbol || it->id() == ID_member)
      {
        bool found=false;
        for(const auto &i:dynobj_instances)
        {
          unsigned long n;
          found |= !i.second.get_number(*it, n);
        }
        if (!found)
        {
            // 1) now make derefence
            const auto &values=
              static_cast<dynobj_instance_analysist &>(ai).value_analysis[loc];
            const auto guard_deref = dereference(guard, values, "", ns);
            auto value_set = values(guard_deref, ns).value_set;
            // 2) then isolate for all values in vaulue set of dereferences
            for (auto &v : value_set)
            {
              auto &instances = dynobj_instances[v.symbol_expr()];
              instances.isolate(*it);
            }
        }
      }
      else
      {
        rhs_concretisation(*it, loc, ai, ns);
      }
    }
}

void dynobj_instance_domaint::transform(
  ai_domain_baset::locationt from,
  ai_domain_baset::locationt to,
  ai_baset &ai,
  const namespacet &ns)
{
  if (from->is_assign()) {
    const code_assignt &assignment = to_code_assign(from->code);
    const exprt lhs = symbolic_dereference(assignment.lhs(), ns);

    if(lhs.id()==ID_symbol &&
       id2string(to_symbol_expr(lhs).get_identifier()).find("__CPROVER")!=
       std::string::npos)
      return;

    if (assignment.rhs().get_bool("#malloc_result"))
    {
      const auto &values=
        static_cast<dynobj_instance_analysist &>(ai).value_analysis[to];
      const auto lhs_deref = dereference(assignment.lhs(), values, "", ns);
      auto value_set = values(lhs_deref, ns).value_set;
      for (auto &v : value_set)
        dynobj_instances[v.symbol_expr()].isolate(lhs);
    }
    else
    {
      exprt rhs = assignment.rhs();
      if (rhs.id() == ID_typecast)
        rhs = to_typecast_expr(rhs).op();

      const auto &values=
        static_cast<dynobj_instance_analysist &>(ai).value_analysis[from];
      const auto rhs_deref = dereference(rhs, values, "", ns);
      auto value_set = values(rhs_deref, ns).value_set;
      for (auto &v : value_set)
      {
        auto &instances = dynobj_instances[v.symbol_expr()];
        instances.isolate(assignment.lhs());
        instances.make_union(assignment.lhs(), rhs);

        remove_dereferences(assignment.lhs(), instances);
        add_aliased_dereferences(assignment.lhs(), instances);

        live_pointers[v.symbol_expr()].insert(rhs);
      }
    }
  }
  else if (from->is_goto() || from->is_assume())
    rhs_concretisation(from->guard, from, ai, ns);
  else if (from->is_dead())
  {
    const exprt &symbol = to_code_dead(from->code).symbol();
    const auto &values=
      static_cast<dynobj_instance_analysist &>(ai).value_analysis[from];
    auto value_set = values(symbol, ns).value_set;
    for (auto &v : value_set)
    {
      live_pointers[v.symbol_expr()].erase(symbol);
    }
  }
}

bool dynobj_instance_domaint::merge(
  const dynobj_instance_domaint &other,
  ai_domain_baset::locationt from,
  ai_domain_baset::locationt to)
{
  bool result = false;
  for (auto &obj : other.dynobj_instances)
  {
    if (dynobj_instances.find(obj.first) == dynobj_instances.end())
    {
      dynobj_instances.insert(obj);
      result = true;
    }
    else
    {
      if (dynobj_instances.at(obj.first).join(obj.second))
        result = true;
    }

    if (other.live_pointers.find(obj.first) != other.live_pointers.end())
    {
      auto &other_pointers = other.live_pointers.at(obj.first);
      live_pointers[obj.first].insert(
        other_pointers.begin(), other_pointers.end());
    }
  }
  return result;
}

void dynobj_instance_domaint::output(
  std::ostream &out,
  const ai_baset &ai,
  const namespacet &ns) const
{
  for (const auto &o : dynobj_instances)
  {
    out << o.first.get_identifier() << ":\n";
    for (const exprt &p : o.second)
    {
      unsigned long n;
      o.second.get_number(p, n);
      out << "    " << o.second.find_number(n) << ": " << from_expr(ns, "", p) << "\n";
    }

    if (live_pointers.find(o.first) == live_pointers.end())
      continue;
    out << "Live: ";
    for (const auto &v : live_pointers.at(o.first))
    {
      out << from_expr(ns, "", v) << " ";
    }
    out << "\n";
  }
}
