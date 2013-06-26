/*******************************************************************\

Module: SSA Showing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <goto-programs/read_goto_binary.h>
#include <goto-programs/goto_model.h>

#include "index.h"
#include "ssa_domain.h"

/*******************************************************************\

Function: show_defs

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void show_defs(
  const goto_functionst::goto_functiont &goto_function,
  const namespacet &ns,
  std::ostream &out)
{
  static_analysist<ssa_domaint> ssa_analysis(ns);
  ssa_analysis(goto_function.body);
  ssa_analysis.output(goto_function.body, out);
}

/*******************************************************************\

Function: show_defs

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void show_defs(
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
    
      out << ">>>> Function " << id << " in " << file_it->first
          << std::endl;
          
      show_defs(*index_fkt, ns, out);
      
      out << std::endl;
    }
  }
  
}
