/*******************************************************************\

Module: Analysis of the number of instances of abstract dynamic objects.
        In some cases, multiple instances must be used so that the
        analysis is sound.

Author: Viktor Malik, viktor.malik@gmail.com

\*******************************************************************/

/// \file
/// Analysis of the number of instances of abstract dynamic objects. In some
///   cases, multiple instances must be used so that the analysis is sound.

#include <iostream>
#include <util/prefix.h>
#include <util/cprover_prefix.h>
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

/// Isolate all dereferences of some pointer in must-alias paritioning.
void remove_dereferences(const exprt &pointer, must_alias_setst &instances)
{
  for(auto &i : instances)
  {
    if(has_deref_of(i, pointer))
      instances.isolate(i);
  }
}

/// Replace pointer in derefence expression by another pointer.
void replace_pointer_in_deref(exprt &deref, const exprt &src, const exprt &dest)
{
  if(deref.id()==ID_dereference && to_dereference_expr(deref).pointer()==src)
    deref=dereference_exprt(dest, deref.type());

  Forall_operands(it, deref)replace_pointer_in_deref(*it, src, dest);
}

/// Add dereferences of all aliased pointers to instances. When dereference of a
/// pointer is put to some must-alias equivalence class, dereferences of aliased
/// pointers must be added to the same class as well.
void add_aliased_dereferences(const exprt &pointer, must_alias_setst &instances)
{
  // We must copy instances so that we can alter them while iterating
  auto inst_copy=instances;
  for(auto &i : inst_copy)
  {
    if(i.id()==ID_symbol && pointer.id()==ID_symbol && i!=pointer &&
       instances.same_set(i, pointer))
    {
      for(auto &deref_i : inst_copy)
      {
        if(has_deref_of(deref_i, i))
        {
          exprt deref_copy=deref_i;
          replace_pointer_in_deref(deref_copy, i, pointer);
          instances.make_union(deref_i, deref_copy);
        }
      }
    }
  }
}

/// Concretise pointer expressions that occur at some RHS and did not occur
/// before (assume they do not alias with anything).
void dynobj_instance_domaint::rhs_concretisation(
  const exprt &guard,
  ai_domain_baset::locationt loc,
  ai_baset &ai,
  const namespacet &ns)
{
  forall_operands(it, guard)
    {
      if(it->id()==ID_symbol || it->id()==ID_member)
      {
        bool found=false;
        for(const auto &i : must_alias_relations)
        {
          size_t n;
          found|=!i.second.get_number(*it, n);
        }
        if(!found)
        {
          // 1) now make dereference
          const auto &values=
            static_cast<dynobj_instance_analysist &>(ai).value_analysis[loc];
          const auto guard_deref=dereference(guard, values, "", ns);
          auto value_set=values(guard_deref, ns).value_set;
          // 2) then isolate for all values in value set of dereferences
          for(auto &v : value_set)
          {
            auto &instances=must_alias_relations[v.symbol_expr()];
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
  if(from->is_assign())
  {
    const code_assignt &assignment=to_code_assign(from->code);
    const exprt lhs=symbolic_dereference(assignment.lhs(), ns);

    // Do not include CPROVER symbols
    if(lhs.id()==ID_symbol &&
       has_prefix(
         id2string(to_symbol_expr(lhs).get_identifier()),
         CPROVER_PREFIX))
      return;

    if(assignment.rhs().get_bool("#malloc_result"))
    {
      // For allocation site, the assigned pointer has no aliases
      const auto &values=
        static_cast<dynobj_instance_analysist &>(ai).value_analysis[to];
      const auto lhs_deref=dereference(assignment.lhs(), values, "", ns);
      auto value_set=values(lhs_deref, ns).value_set;
      for(auto &v : value_set)
        must_alias_relations[v.symbol_expr()].isolate(lhs);
    }
    else
    {
      // For other assignments, use value analysis to get all pointers pointing
      // to a dynamic object and then update must-alias sets.
      exprt rhs=assignment.rhs();
      if(rhs.id()==ID_typecast)
        rhs=to_typecast_expr(rhs).op();

      const auto &values=
        static_cast<dynobj_instance_analysist &>(ai).value_analysis[from];
      const auto rhs_deref=dereference(rhs, values, "", ns);
      auto value_set=values(rhs_deref, ns).value_set;
      for(auto &v : value_set)
      {
        auto &instances=must_alias_relations[v.symbol_expr()];
        instances.isolate(assignment.lhs());
        instances.make_union(assignment.lhs(), rhs);

        remove_dereferences(assignment.lhs(), instances);
        add_aliased_dereferences(assignment.lhs(), instances);

        // Do not include CPROVER objects
        // TODO: do it better than check for "malloc" substring
        if(!(rhs.id()==ID_symbol &&
          (id2string(to_symbol_expr(rhs).get_identifier()).find(
               "malloc::")!=std::string::npos ||
           id2string(to_symbol_expr(rhs).get_identifier()).find(
             "malloc#")!=std::string::npos ||
           id2string(to_symbol_expr(rhs).get_identifier()).find(
             "malloc$")!=std::string::npos)))
        {
          live_pointers[v.symbol_expr()].insert(rhs);
        }
      }
    }
  }
  else if(from->is_goto() || from->is_assume() || from->is_assert())
    rhs_concretisation(from->guard, from, ai, ns);
  else if(from->is_dead())
  {
    const exprt &symbol=to_code_dead(from->code).symbol();
    const auto &values=
      static_cast<dynobj_instance_analysist &>(ai).value_analysis[from];
    auto value_set=values(symbol, ns).value_set;
    for(auto &v : value_set)
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
  bool result=false;
  for(auto &obj : other.must_alias_relations)
  {
    if(must_alias_relations.find(obj.first)==must_alias_relations.end())
    {
      must_alias_relations.insert(obj);
      result=true;
    }
    else
    {
      if(must_alias_relations.at(obj.first).join(obj.second))
        result=true;
    }

    if(other.live_pointers.find(obj.first)!=other.live_pointers.end())
    {
      auto &other_pointers=other.live_pointers.at(obj.first);
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
  for(const auto &o : must_alias_relations)
  {
    out << o.first.get_identifier() << ":\n";
    for(const exprt &p : o.second)
    {
      size_t n;
      o.second.get_number(p, n);
      out << "    " << o.second.find_number(n) << ": " << from_expr(ns, "", p)
          << "\n";
    }

    if(live_pointers.find(o.first)==live_pointers.end())
      continue;
    out << "Live: ";
    for(const auto &v : live_pointers.at(o.first))
    {
      out << from_expr(ns, "", v) << " ";
    }
    out << "\n";
  }
}
