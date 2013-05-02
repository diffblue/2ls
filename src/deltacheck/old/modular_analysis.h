/*******************************************************************\

Module: Partial fixed-point analysis to be used for function-pointer alias 
analysis per C file.

The analysis accepts rules (subsumption among variables), values (constants),
and distinguishes visible and invisible variables. After fixpoint computation
the invisible variables can be removed.

Author: Ondrej Sery, ondrej.sery@d3s.mff.cuni.cz

\*******************************************************************/

#ifndef CPROVER_DELTACHECK_PARTIAL_ANALYSIS_H
#define	CPROVER_DELTACHECK_PARTIAL_ANALYSIS_H

#include <iostream>

#include <util/hash_cont.h>

template <typename variableT, typename valueT,
          typename variable_hashT, typename value_hashT>
class modular_analysist {
public:
  typedef variableT variablet;
  typedef valueT valuet;
  typedef typename hash_set_cont<valuet, value_hashT> valuest;
  typedef typename hash_set_cont<variablet, variable_hashT> variablest;
  typedef typename hash_map_cont<variablet, valuest, variable_hashT> value_mapt;
  typedef typename hash_map_cont<variablet, variablest, variable_hashT> rulest;
  
  modular_analysist() {}
  
  bool add_rule(const variablet& subsumes, 
          const variablet& subsumed)
  {
    insert_variable(inverse_rules, subsumed, subsumes);
    return insert_variable(rules, subsumes, subsumed);
  }
  
  bool add_value(const variablet& variable, const valuet& value)
  {
    typename value_mapt::iterator it = value_map.find(variable);
    
    if (it == value_map.end())
      it = value_map.insert(typename value_mapt::value_type(
              variable, valuest())).first;
    
    unsigned count = it->second.size();
    it->second.insert(value);
    
    return count != it->second.size();
  }
  
  bool add_values(const variablet& variable, const valuest& values)
  {
    typename value_mapt::iterator it = value_map.find(variable);
    
    if (it == value_map.end())
      it = value_map.insert(
              typename value_mapt::value_type(variable, valuest())).first;
    
    unsigned count = it->second.size();
    it->second.insert(values.begin(), values.end());
    
    return count != it->second.size();
  }
  
  void set_visible(const variablet& variable)
  {
    visible_variables.insert(variable);
  }
  
  void compute_fixpoint()
  {
    variablest queue;
    
    // Only variables occurring as rhs of a rule need to be considered
    for (typename rulest::const_iterator 
            it = rules.begin();
            it != rules.end();
            ++it)
    {
      queue.insert(it->first);
    }
    
    // Iterate until saturation
    while (!queue.empty())
    {
      variablet current = *queue.begin();
      queue.erase(queue.begin());
      
      bool changed = update_variable(current);
      
      if (changed)
        plan_dependants(queue, current);
    }
  }
  
  void remove_invisible() 
  {
    remove_invisible_from_values();
    remove_invisible_from_rules(rules);
    remove_invisible_from_rules(inverse_rules);
  }
  
  const value_mapt& get_value_map() const { return value_map; }
  
private:
  
  bool insert_variable(rulest& rules, const variablet& key, 
          const variablet& value)
  {
    typename rulest::iterator it = rules.find(key);
    
    if (it == rules.end())
      it = rules.insert(typename rulest::value_type(key, variablest())).first;
    
    unsigned count = it->second.size();
    it->second.insert(value);
    
    return count != it->second.size();
  }
  
  void remove_invisible_from_values()
  {
    for (typename value_mapt::const_iterator it = value_map.begin();
            it != value_map.end();)
    {
      if (visible_variables.find(it->first) == visible_variables.end()) 
        it = value_map.erase(it);
      else 
        ++it;
    }
  }
  
  void remove_invisible_from_rules(rulest& rules)
  {
    for (typename rulest::iterator it = rules.begin();
            it != rules.end();)
    {
      if (visible_variables.find(it->first) == visible_variables.end()) 
      {
        // Invisible key -> remove the whole entry
        it = rules.erase(it);
      }
      else 
      {
        // Visible key -> remove invisible values
        variablest& variables = it->second;
        for (typename variablest::const_iterator it2 = variables.begin();
                it2 != variables.end();) 
        {
          if (visible_variables.find(*it2) == visible_variables.end())
            it2 = variables.erase(it2);
          else
            ++it2;
        }
        
        // All values removed -> remove the whole entry anyway
        if (variables.size() == 0)
          it = rules.erase(it);
        else
          ++it;
      }
    }
  }
  
  bool update_variable(const variablet& variable) 
  {
    bool changed = false;
    
    typename rulest::const_iterator it = rules.find(variable);
    
    if (it == inverse_rules.end())
      return false;
    
    // Merge the values and rules
    for (typename variablest::const_iterator it2 = it->second.begin();
            it2 != it->second.end();
            ++it2)
    {
      if (*it2 != variable) {
        if (visible_variables.find(*it2) == visible_variables.end()) {
          changed |= merge_rules(variable, *it2);
        }
        changed |= merge_values(variable, *it2);
      }
    }
    
    return changed;
  }
  
  bool merge_rules(const variablet& dest, const variablet& src)
  {
    typename rulest::const_iterator it = rules.find(src);
    
    if (it == rules.end())
      return false;
    
    bool changed = false;
    
    for (typename variablest::const_iterator it2 = it->second.begin();
            it2 != it->second.end();
            ++it2)
    {
      changed |= add_rule(dest, *it2);
    }
    return changed;
  }
  
  bool merge_values(const variablet& dest, const variablet& src)
  {
    typename value_mapt::const_iterator it = value_map.find(src);
    
    if (it == value_map.end())
      return false;
    
    return add_values(dest, it->second);
  }
  
  void plan_dependants(variablest& queue, const variablet& variable)
  {
    typename rulest::const_iterator it = inverse_rules.find(variable);
    
    if (it == inverse_rules.end())
      return;
    
    for (typename variablest::const_iterator it2 = it->second.begin();
            it2 != it->second.end();
            ++it2)
    {
      if (*it2 != variable)
        queue.insert(*it2);
    }
  }

protected:
  value_mapt value_map;
  rulest rules;
  rulest inverse_rules;
  variablest visible_variables;
};

#endif

