//
// Created by vmalik on 5/14/18.
//

#ifndef INC_2LS_DYNOBJ_INSTANCE_ANALYSIST_H
#define INC_2LS_DYNOBJ_INSTANCE_ANALYSIST_H


#include <analyses/ai.h>
#include <util/union_find.h>
#include "ssa_object.h"
#include "ssa_value_set.h"

class must_alias_setst : public union_find<exprt>
{
protected:
  bool equal(const must_alias_setst &other)
  {
    if (size() != other.size())
      return false;

    for (auto &e1 : *this)
    {
      unsigned long n;
      if (other.get_number(e1, n))
        return false;
      for (auto &e2 : *this)
        if (same_set(e1, e2) != other.same_set(e1, e2))
          return false;
    }
    return true;
  }

  std::set<exprt> sym_diff_elements(const must_alias_setst &other)
  {
    std::set<exprt> result;
    unsigned long n;
    for (auto &e : *this)
      if (get_number(e, n))
        result.insert(e);
    for (auto &e : other)
      if (get_number(e, n))
        result.insert(e);
    return result;
  }

public:
  bool join(const must_alias_setst &other)
  {
    if (!equal(other))
    {
      // Find new elements (those that are unique to one of the sets
      auto new_elements = sym_diff_elements(other);
      // Copy *this
      auto original = *this;

      // Make intersection (into *this) which contains all common elements
      // (after retyping to vector)
      clear();
      std::set<exprt> common_elements;
      for (auto &e1 : original)
      {
        if (new_elements.find(e1) != new_elements.end())
          continue;

        isolate(e1);
        for (auto &e2 : common_elements)
          if (original.same_set(e1, e2) && other.same_set(e1, e2))
            make_union(e1, e2);
        common_elements.insert(e1);
      }

      for (auto &e_new : new_elements)
      {
        bool added = false;
        // First, try to find some new element that is already in *this and that
        // is in the same class as e_new in one of the sets
        for (auto &e : *this)
        {
          if(new_elements.find(e)!=new_elements.end() &&
             (original.same_set(e, e_new) || other.same_set(e, e_new)))
          {
            make_union(e, e_new);
            added = true;
          }
        }
        if (!added)
        {
          // Find all sets to which e_new should be added by comparing with
          // common elements
          // The map will contain: set_number(in *this) -> set_representative
          std::map<unsigned long, exprt> dest_sets;
          for(auto &e: common_elements)
          {
            if(original.same_set(e_new, e) || other.same_set(e_new, e))
            {
              unsigned long n;
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
};

class dynobj_instance_domaint:public ai_domain_baset
{
public:
  std::map<symbol_exprt, must_alias_setst> dynobj_instances;
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

protected:

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


#endif //INC_2LS_DYNOBJ_INSTANCE_ANALYSIST_H
