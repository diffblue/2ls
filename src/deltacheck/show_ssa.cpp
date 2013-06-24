/*******************************************************************\

Module: SSA Showing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <goto-programs/read_goto_binary.h>
#include <goto-programs/goto_model.h>

#include "index.h"
#include "function_ssa.h"

/*******************************************************************\

Function: show_ssa

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void show_ssa(
  const goto_functionst::goto_functiont &goto_function,
  const namespacet &ns,
  std::ostream &out)
{
  function_SSAt function_SSA(goto_function, ns);
  function_SSA.output(out);
}

/*******************************************************************\

Function: show_ssa

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void show_ssa(
  const indext &index,
  std::ostream &out,
  message_handlert &message_handler)
{
  for(indext::file_to_functiont::const_iterator
      file_it=index.file_to_function.begin();
      file_it!=index.file_to_function.end();
      file_it++)
  {
    // read the file
    goto_modelt model;
    read_goto_binary(id2string(file_it->first), model, message_handler);
    
    const namespacet ns(model.symbol_table);
    const std::set<irep_idt> &functions=file_it->second;

    // now do all functions from model
    for(std::set<irep_idt>::const_iterator
        fkt_it=functions.begin();
        fkt_it!=functions.end();
        fkt_it++)
    {
      const irep_idt &id=*fkt_it;
      const goto_functionst::goto_functiont *index_fkt=
        &model.goto_functions.function_map.find(id)->second;
    
      out << "**** Function " << id << " in " << file_it->first
          << std::endl;
          
      show_ssa(*index_fkt, ns, out);
    }
  }
  
}
