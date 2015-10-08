/*******************************************************************\

Module: Indexing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <goto-programs/read_goto_binary.h>

#include "path_util.h"
#include "get_function.h"

/*******************************************************************\

Function: get_functiont::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

goto_functionst::goto_functiont * get_functiont::operator()(const irep_idt &id)
{
  // do we have it in our current file?
  if(current_file_name!="")
  {
    const goto_functionst::function_mapt::iterator
      f_it=goto_model.goto_functions.function_map.find(id);
    
    if(f_it!=goto_model.goto_functions.function_map.end())
      return &f_it->second; // found
  }
  
  // find in index
  indext::function_to_filet::const_iterator it=
    index.function_to_file.find(id);
   
  if(it==index.function_to_file.end())
    return NULL; // not there
  
  // pick first file
  assert(!it->second.empty());
  
  irep_idt file_name=*(it->second.begin());

  current_file_name=index.full_path(file_name);
  
  status() << "Reading \"" << id2string(current_file_name) << "\"" << eom;
  
  // read the file
  goto_model.clear();

  bool error=read_goto_binary(
    id2string(current_file_name),
    goto_model,
    get_message_handler());
  
  if(error)
    return NULL;

  const goto_functionst::function_mapt::iterator
    f_it=goto_model.goto_functions.function_map.find(id);
  
  assert(f_it!=goto_model.goto_functions.function_map.end());
  return &f_it->second;
}
