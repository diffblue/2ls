/*******************************************************************\

Module: Change Impact

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_DELTACHECK_CHANGE_IMPACT_H
#define CPROVER_DELTACHECK_CHANGE_IMPACT_H

#include <stack>

#include <util/options.h>

#include "get_function.h"
#include "index.h"

class change_impactt:public messaget
{
public:
  struct f_idt
  {
    irep_idt file, function_id;
  };
  
  friend bool operator<(const f_idt &f1, const f_idt &f2)
  {
    if(f1.file<f2.file) return true;
    if(f1.file!=f2.file) return false;
    return f1.function_id<f2.function_id;
  }

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
    
    std::set<f_idt> calls;
    std::set<f_idt> called_by;
  };

  // functions to 'affected' map
  typedef std::map<irep_idt, datat> function_mapt;
  
  // file to functions map
  typedef std::map<irep_idt, function_mapt> file_mapt;
  file_mapt file_map;

  void diff(
    const indext &old_index,
    const indext &new_index,
    const optionst &options);

  void change_impact(
    const indext &new_index,
    const optionst &options);

  void output_diff(std::ostream &);  
  void output_change_impact(std::ostream &);  
  
protected:
  void diff_functions(
    const irep_idt &file,
    const irep_idt &function_id,
    const goto_functionst::goto_functiont &,
    const goto_functionst::goto_functiont &);

  void propagate_affected(
    const indext &new_index,
    get_functiont &get_function,
    const optionst &options,
    const f_idt &f_id,
    std::stack<f_idt> &working);

  void make_fully_affected(const f_idt &f_id);
  
  void do_call_graph(
    const indext &index,
    const irep_idt &file,
    const goto_modelt &);
  
  f_idt get_f_id(
    const indext &index,
    const irep_idt &file,
    const irep_idt &function_id)
  {
    f_idt result;
    result.file=index.get_file_for_function(file, function_id);
    result.function_id=function_id;
    return result;
  }
};

#endif
