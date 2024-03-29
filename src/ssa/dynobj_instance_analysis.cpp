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
#include <util/pointer_expr.h>
#include <langapi/language_util.h>
#include "dynobj_instance_analysis.h"
#include "dynamic_objects.h"
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
  for(auto &i : instances.data)
  {
    if(has_deref_of(i, pointer))
      instances.data.isolate(i);
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
  for(auto &i : inst_copy.data)
  {
    if(i.id()==ID_symbol && pointer.id()==ID_symbol && i!=pointer &&
       instances.data.same_set(i, pointer))
    {
      for(auto &deref_i : inst_copy.data)
      {
        if(has_deref_of(deref_i, i))
        {
          exprt deref_copy=deref_i;
          replace_pointer_in_deref(deref_copy, i, pointer);
          instances.data.make_union(deref_i, deref_copy);
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
          found|=!i.second.data.get_number(*it);
        }
        if(!found)
        {
          // 1) now make dereference
          const auto &values=
            static_cast<dynobj_instance_analysist &>(ai).value_analysis[loc];
          bool competition_mode=
            static_cast<dynobj_instance_analysist &>(ai).options
              .get_bool_option("competition-mode");
          const auto guard_deref=dereference(
            guard, values, "", ns, competition_mode);
          auto value_set=values(guard_deref, ns).value_set;
          // 2) then isolate for all values in value set of dereferences
          for(auto &v : value_set)
          {
            auto &instances=must_alias_relations[v.symbol_expr()];
            instances.data.isolate(*it);
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
  const irep_idt &function_from,
  trace_ptrt trace_from,
  const irep_idt &function_to,
  trace_ptrt trace_to,
  ai_baset &ai,
  const namespacet &ns)
{
  locationt from{trace_from->current_location()};

  auto dynamic_objects=
    dynamic_cast<dynobj_instance_analysist &>(ai).dynamic_objects;
  bool competition_mode=
    static_cast<dynobj_instance_analysist &>(ai).options
      .get_bool_option("competition-mode");
  if(from->is_assign())
  {
    const exprt &assign_lhs=from->assign_lhs();
    const exprt &assign_rhs=from->assign_rhs();
    const exprt lhs=symbolic_dereference(assign_lhs, ns);

    // Do not include CPROVER symbols
    if(lhs.id()==ID_symbol &&
       has_prefix(
         id2string(to_symbol_expr(lhs).get_identifier()),
         CPROVER_PREFIX))
      return;

    if(dynamic_objects.have_objects(*from))
    {
      for(auto &obj : dynamic_objects.get_objects(*from))
        must_alias_relations[obj.symbol_expr()].data.isolate(lhs);
    }
    else
    {
      // For other assignments, use value analysis to get all pointers pointing
      // to a dynamic object and then update must-alias sets.
      exprt rhs=assign_rhs; // copy
      if(rhs.id()==ID_typecast)
        rhs=to_typecast_expr(rhs).op();

      const auto &values=
        dynamic_cast<dynobj_instance_analysist &>(ai).value_analysis[from];
      const auto rhs_deref=dereference(rhs, values, "", ns, competition_mode);
      auto value_set=values(rhs_deref, ns).value_set;
      for(auto &v : value_set)
      {
        auto &instances=must_alias_relations[v.symbol_expr()];
        instances.data.isolate(assign_lhs);
        instances.data.make_union(assign_lhs, rhs);

        remove_dereferences(assign_lhs, instances);
        add_aliased_dereferences(assign_lhs, instances);

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
    rhs_concretisation(from->condition(), from, ai, ns);
  else if(from->is_dead())
  {
    const exprt &symbol=from->dead_symbol();
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
  trace_ptrt trace_from,
  trace_ptrt trace_to)
{
  bool result=has_values.is_false() && !other.has_values.is_false();
  has_values=tvt::unknown();
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
    for(const exprt &p : o.second.data)
    {
      size_t n;
      const auto number=o.second.data.get_number(p);
      if(!number)
        continue;
      n=*number;
      out << "    " << o.second.data.find_number(n)
          << ": " << from_expr(ns, "", p)
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

void dynobj_instance_analysist::initialize(
  const irep_idt &function_id,
  const goto_programt &goto_program)
{
  forall_goto_program_instructions(i_it, goto_program)
    get_state(i_it).make_bottom();
}
