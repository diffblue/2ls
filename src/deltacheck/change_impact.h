/*******************************************************************\

Module: Change Impact

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_DELTACHECK_CHANGE_IMPACT_H
#define CPROVER_DELTACHECK_CHANGE_IMPACT_H

#include <stack>

class change_impactt:public messaget
{
public:
  void diff(
    const goto_modelt &old_model,
    const goto_modelt &new_model);

  void change_impact(
    const goto_modelt &new_model);

  void output_diff(std::ostream &);  
  void output_change_impact(std::ostream &);  
  
  struct datat
  {
    datat():
      fully_changed(false),
      fully_affected(false)
    {
    }
    
    bool has_change() const
    {
      return fully_changed || !locs_changed.empty();
    }
    
    bool is_affected() const
    {
      return fully_affected || !locs_affected.empty();
    }
    
    bool fully_changed, fully_affected;
    std::set<unsigned> locs_changed, locs_affected;
    
    std::set<irep_idt> calls;
    std::set<irep_idt> called_by;
  };

  // functions to 'datat' map
  typedef std::map<irep_idt, datat> function_mapt;
  function_mapt function_map;

protected:
  void diff_functions(
    const irep_idt &function_id,
    const goto_functionst::goto_functiont &,
    const goto_functionst::goto_functiont &);

  void propagate_affected(
    const goto_modelt &new_index,
    const irep_idt &id,
    std::stack<irep_idt> &working);

  void make_fully_affected(const irep_idt &);
  
  void do_call_graph(
    const goto_modelt &);
};

#endif
