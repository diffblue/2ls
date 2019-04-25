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
#include "ssa_object.h"
#include "ssa_value_set.h"

class must_alias_setst:public union_find<exprt>
{
public:
  bool join(const must_alias_setst &other)
  {
    if(!equal(other))
    {
      // Find new elements (those that are unique to one of the sets)
      auto new_elements=sym_diff_elements(other);
      // Copy *this
      auto original=*this;

      // Make intersection (into *this) which contains all common elements
      // (after retyping to vector)
      clear();
      std::set<exprt> common_elements;
      for(auto &e1 : original)
      {
        if(new_elements.find(e1)!=new_elements.end())
          continue;

        isolate(e1);
        for(auto &e2 : common_elements)
          if(original.same_set(e1, e2) && other.same_set(e1, e2))
            make_union(e1, e2);
        common_elements.insert(e1);
      }

      for(auto &e_new : new_elements)
      {
        bool added=false;
        // First, try to find some new element that is already in *this and that
        // is in the same class as e_new in one of the sets
        auto this_copy(*this);
        for(auto &e : this_copy)
        {
          if(new_elements.find(e)!=new_elements.end() &&
             (original.same_set(e, e_new) || other.same_set(e, e_new)))
          {
            make_union(e, e_new);
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
            if(original.same_set(e_new, e) || other.same_set(e_new, e))
            {
              size_t n;
              get_number(e, n);
              if(dest_sets.find(n)==dest_sets.end())
                dest_sets.emplace(n, e);
            }
          }

          // If there is just one set to add e_new to, add it there, otherwise
          // isolate it
          if(dest_sets.size()==1)
            make_union(e_new, dest_sets.begin()->second);
          else
            isolate(e_new);
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
    if(size()!=other.size())
      return false;

    for(auto &e1 : *this)
    {
      size_t n;
      if(other.get_number(e1, n))
        return false;
      for(auto &e2 : *this)
        if(same_set(e1, e2)!=other.same_set(e1, e2))
          return false;
    }
    return true;
  }

  // Symmetric difference of elements
  std::set<exprt> sym_diff_elements(const must_alias_setst &other)
  {
    std::set<exprt> result;
    size_t n;
    for(auto &e : *this)
      if(get_number(e, n))
        result.insert(e);
    for(auto &e : other)
      if(get_number(e, n))
        result.insert(e);
    return result;
  }
};

class dynobj_instance_domaint:public ai_domain_baset
{
public:
  // Must-alias relation for each dynamic object (corresponding to allocation
  // site).
  std::map<symbol_exprt, must_alias_setst> must_alias_relations;
  // Set of live pointers pointing to dynamic object.
  std::map<symbol_exprt, std::set<exprt>> live_pointers;

  void transform(
    locationt from,
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
    const goto_functionst::goto_functiont &goto_function,
    const namespacet &ns,
    ssa_value_ait &_value_ai):
    value_analysis(_value_ai)
  {
    operator()(goto_function, ns);
  }

protected:
  ssa_value_ait &value_analysis;

  friend class dynobj_instance_domaint;
};

#endif // CPROVER_2LS_SSA_DYNOBJ_INSTANCE_ANALYSIS_H
