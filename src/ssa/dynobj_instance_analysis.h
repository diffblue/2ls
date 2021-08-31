/*******************************************************************\

Module: Analysis of the number of instances of abstract dynamic objects.

Author: Viktor Malik, viktor.malik@gmail.com

Description: In some cases, multiple instances must be used so that the
             analysis is sound. The analysis computes for each allocation
             site 'a' and each program location 'i' a set of pointer
             expressions that may point to some object allocated at 'a'
             in the location 'i'. Then, a must-alias relation is computed
             over these sets and the maximum number of equivalence classes
             gives the number of required objects for the given allocation
             site.

\*******************************************************************/

/// \file
/// Analysis of the number of instances of abstract dynamic objects.

#ifndef CPROVER_2LS_SSA_DYNOBJ_INSTANCE_ANALYSIS_H
#define CPROVER_2LS_SSA_DYNOBJ_INSTANCE_ANALYSIS_H


#include <analyses/ai.h>
#include <util/union_find.h>
#include <util/options.h>
#include <util/threeval.h>
#include "ssa_object.h"
#include "ssa_value_set.h"

class must_alias_setst
{
public:
  union_find<exprt> data;

  bool join(const must_alias_setst &other)
  {
    if(!equal(other))
    {
      // Find new elements (those that are unique to one of the sets)
      auto new_elements=sym_diff_elements(other);
      // Copy the union find
      auto original=data;

      // Make intersection (into *this) which contains all common elements
      // (after retyping to vector)
      data.clear();
      std::set<exprt> common_elements;
      for(auto &e1 : original)
      {
        if(new_elements.find(e1)!=new_elements.end())
          continue;

        data.isolate(e1);
        for(auto &e2 : common_elements)
          if(original.same_set(e1, e2) && other.data.same_set(e1, e2))
            data.make_union(e1, e2);
        common_elements.insert(e1);
      }

      for(auto &e_new : new_elements)
      {
        bool added=false;
        // First, try to find some new element that is already in *this and that
        // is in the same class as e_new in one of the sets
        auto union_find_copy(data);
        for(auto &e : union_find_copy)
        {
          if(new_elements.find(e)!=new_elements.end() &&
             (original.same_set(e, e_new) || other.data.same_set(e, e_new)))
          {
            data.make_union(e, e_new);
            added=true;
          }
        }
        if(!added)
        {
          // Find all sets to which e_new should be added by comparing with
          // common elements
          // The map will contain: set_number(in *this) -> set_representative
          std::map<size_t, exprt> dest_sets;
          for(auto &e : common_elements)
          {
            if(original.same_set(e_new, e) ||
              other.data.same_set(e_new, e))
            {
              size_t n;
              const auto number=data.get_number(e);
              if(!number)
                continue;
              n=*number;
              if(dest_sets.find(n)==dest_sets.end())
                dest_sets.emplace(n, e);
            }
          }

          // If there is just one set to add e_new to, add it there, otherwise
          // isolate it
          if(dest_sets.size()==1)
            data.make_union(e_new, dest_sets.begin()->second);
          else
            data.isolate(e_new);
        }
      }
      return true;
    }
    return false;
  }

protected:
  // Two partitionings are equal if they contain same elements partitioned
  // in same sets (not necessarily having same numbers).
  bool equal(const must_alias_setst &other)
  {
    if(data.size()!=other.data.size())
      return false;

    for(auto &e1 : data)
    {
      if(!other.data.get_number(e1))
        return false;
      for(auto &e2 : data)
        if(data.same_set(e1, e2)!=other.data.same_set(e1, e2))
          return false;
    }
    return true;
  }

  // Symmetric difference of elements
  std::set<exprt> sym_diff_elements(const must_alias_setst &other)
  {
    std::set<exprt> result;
    for(auto &e : data)
      if(!data.get_number(e))
        result.insert(e);
    for(auto &e : other.data)
      if(!data.get_number(e))
        result.insert(e);
    return result;
  }
};

class dynobj_instance_domaint:public ai_domain_baset
{
public:
  dynobj_instance_domaint(): has_values(false) {}

  // Must-alias relation for each dynamic object (corresponding to allocation
  // site).
  std::map<symbol_exprt, must_alias_setst> must_alias_relations;
  // Set of live pointers pointing to dynamic object.
  std::map<symbol_exprt, std::set<exprt>> live_pointers;

  void transform(
    const irep_idt &,
    locationt from,
    const irep_idt &,
    locationt to,
    ai_baset &ai,
    const namespacet &ns) override;
  void output(
    std::ostream &out,
    const ai_baset &ai,
    const namespacet &ns) const override;
  bool merge(
    const dynobj_instance_domaint &other,
    locationt from,
    locationt to);

  void make_bottom() override
  {
    must_alias_relations.clear();
    live_pointers.clear();
    has_values=tvt(false);
  }

  void make_top() override
  {
    must_alias_relations.clear();
    live_pointers.clear();
    has_values=tvt(true);
  }

  void make_entry() override
  {
    make_top();
  }

  bool is_bottom() const override
  {
    return has_values.is_false();
  }

  bool is_top() const override
  {
    return has_values.is_true();
  }

protected:
  tvt has_values;

private:
  void rhs_concretisation(
    const exprt &guard,
    ai_domain_baset::locationt loc,
    ai_baset &ai,
    const namespacet &ns);
};

class dynobj_instance_analysist:public ait<dynobj_instance_domaint>
{
public:
  dynobj_instance_analysist(
    const irep_idt &function_identifier,
    const goto_functionst::goto_functiont &goto_function,
    const namespacet &ns,
    const optionst &_options,
    ssa_value_ait &_value_ai):
    options(_options),
    value_analysis(_value_ai)
  {
    operator()(function_identifier, goto_function, ns);
  }

protected:
  const optionst &options;
  ssa_value_ait &value_analysis;
  void initialize(
    const irep_idt &function_id,
    const goto_programt &goto_program) override;

  friend class dynobj_instance_domaint;
};

#endif // CPROVER_2LS_SSA_DYNOBJ_INSTANCE_ANALYSIS_H
