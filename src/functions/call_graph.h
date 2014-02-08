/*******************************************************************\

Module: Change Impact

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_DELTACHECK_CALL_GRAPH_H
#define CPROVER_DELTACHECK_CALL_GRAPH_H

#include "index.h"

class call_grapht
{
public:
  // function names are not unique
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
    std::set<f_idt> calls;
    std::set<f_idt> called_by;
  };

  // function ID to 'datat' map
  typedef std::map<irep_idt, datat> function_mapt;
  
  // file to functions map
  typedef std::map<irep_idt, function_mapt> file_mapt;
  file_mapt file_map;
  
  inline datat &operator[](const f_idt &f)
  {
    return file_map[f.file][f.function_id];
  }

  void build(
    const indext &index,
    const irep_idt &file,
    const goto_modelt &);
  
protected:
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
