/*******************************************************************\

Module: Partial fixed-point analysis to be used for function-pointer alias 
analysis per C file.

Author: Ondrej Sery, ondrej.sery@d3s.mff.cuni.cz

\*******************************************************************/

#ifndef CPROVER_DELTACHECK_PARTIAL_ANALYSIS_H
#define	CPROVER_DELTACHECK_PARTIAL_ANALYSIS_H

#include <iostream>
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
  
  void remove_invisible() 
  {
    remove_invisible_from_values();
    remove_invisible_from_rules(rules);
    remove_invisible_from_rules(inverse_rules);
  }
  
  const value_mapt& get_value_map() const { return value_map; }
  
  void print(std::ostream& out) const
  {
    // Values
    for (typename value_mapt::const_iterator it = value_map.begin();
            it != value_map.end();
            ++it)
    {
      out << "Values for \"" << it->first << "\" <--" << std::endl;
      
      const valuest& values = it->second;
      for (typename valuest::const_iterator it2 = values.begin();
            it2 != values.end();
            ++it2)
      {
        out << "    \"" << *it2 << "\"" << std::endl;
      }
    }
    // Rules
    for (typename rulest::const_iterator it = rules.begin();
            it != rules.end();
            ++it)
    {
      out << "Rules for \"" << it->first << "\" <--" << std::endl;
      
      const variablest& variables = it->second;
      for (typename variablest::const_iterator it2 = variables.begin();
            it2 != variables.end();
            ++it2)
      {
        out << "    \"" << *it2 << "\"" << std::endl;
      }
    }
  }
  
  void serialize(std::ostream& out)
  {
    // Values
    out << value_map.size() << std::endl;
    for (typename value_mapt::const_iterator it = value_map.begin();
            it != value_map.end();
            ++it)
    {
      const valuest& values = it->second;
      
      out << it->first << std::endl;
      out << values.size() << std::endl;
      
      for (typename valuest::const_iterator it2 = values.begin();
            it2 != values.end();
            ++it2)
      {
        out << *it2 << std::endl;
      }
    }
    // Rules
    out << rules.size() << std::endl;
    for (typename rulest::const_iterator it = rules.begin();
            it != rules.end();
            ++it)
    {
      const variablest& variables = it->second;
      out << it->first << std::endl;
      out << it->second.size() << std::endl;
      
      for (typename variablest::const_iterator it2 = variables.begin();
            it2 != variables.end();
            ++it2)
      {
        out << *it2 << std::endl;
      }
    }
    // Visible variables
    out << visible_variables.size() << std::endl;
    for (typename variablest::const_iterator it = visible_variables.begin();
            it != visible_variables.end();
            ++it)
    {
      out << *it << std::endl;
    }
  }
  
  void deserialize(std::istream& in)
  {
    // Values
    int values_map_size;
    in >> values_map_size;
    if (!in.good()) return;
    
    for (int i = 0; i < values_map_size; ++i)
    {
      int values_size;
      std::string var_str;
      in >> var_str;
      in >> values_size;
      variablet var(var_str);
      if (!in.good()) return;
      
      for (int j = 0; j < values_size; ++j)
      {
        std::string val_str;
        in >> val_str;
        valuet val(val_str);
        
        add_value(var, val);
      }
    }
    // Rules
    int rules_size;
    in >> rules_size;
    if (!in.good()) return;
    
    for (int i = 0; i < rules_size; ++i)
    {
      int vars_size;
      std::string var_str;
      in >> var_str;
      in >> vars_size;
      variablet var(var_str);
      if (!in.good()) return;
      
      for (int j = 0; j < vars_size; ++j)
      {
        std::string var2_str;
        in >> var2_str;
        variablet var2(var2_str);
        
        add_rule(var, var2);
      }
    }
    // Visible variables
    int visible_size;
    in >> visible_size;
    if (!in.good()) return;
    
    for (int i = 0; i < visible_size; ++i)
    {
      std::string var_str;
      in >> var_str;
      variablet var(var_str);
      
      set_visible(var);
    }
  }
  
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
  
  value_mapt value_map;
  rulest rules;
  rulest inverse_rules;
  variablest visible_variables;
  variablest all_variables;
};

#endif

