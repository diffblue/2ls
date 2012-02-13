/*******************************************************************\

Module: Partial fixed-point analysis to be used for function-pointer alias 
analysis per C file.

Author: Ondrej Sery, ondrej.sery@d3s.mff.cuni.cz

\*******************************************************************/

#ifndef CPROVER_DELTACHECK_PARTIAL_ANALYSIS_H
#define	CPROVER_DELTACHECK_PARTIAL_ANALYSIS_H

#include <hash_cont.h>

template <typename variablet, typename valuet, 
        typename variable_hasht, typename value_hasht>
class partial_analysist {
public:
  typedef typename hash_set_cont<valuet, value_hasht> valuest;
  typedef typename hash_set_cont<variablet, variable_hasht> variablest;
  typedef typename hash_map_cont<variablet, valuest, variable_hasht> value_mapt;
  typedef typename hash_map_cont<variablet, variablest, variable_hasht> rulest;
  
  partial_analysist() {}
  
  bool add_rule(const variablet& subsumes, 
          const variablet& subsumed)
  {
    all_variables.insert(subsumes);
    all_variables.insert(subsumed);
    insert_variable(inverse_rules, subsumed, subsumes);
    return insert_variable(rules, subsumes, subsumed);
  }
  
  bool add_value(const variablet& variable, const valuet& value)
  {
    all_variables.insert(variable);
    
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
    all_variables.insert(variable);
    
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
    all_variables.insert(variable);
  }
  
  void find_fixpoint()
  {
    variablest queue(all_variables);
    
    while (!queue.empty())
    {
      variablet current = *queue.begin();
      queue.erase(queue.begin());
      
      bool changed = update_variable(current);
      
      if (changed)
        plan_dependants(queue, current);
    }
  }
  
  void remove_invisible(); // TODO
  
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
        changed |= add_rule(variable, *it2);
        changed |= merge_values(variable, *it2);
      }
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
  
  value_mapt value_map;
  rulest rules;
  rulest inverse_rules;
  variablest visible_variables;
  variablest all_variables;
};

#endif

