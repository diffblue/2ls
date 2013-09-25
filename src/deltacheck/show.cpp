/*******************************************************************\

Module: Showing various debugging information

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/options.h>

#include <goto-programs/read_goto_binary.h>
#include <goto-programs/goto_model.h>
#include <goto-programs/show_properties.h>
#include <goto-programs/set_properties.h>

#include <analyses/goto_check.h>

#include "../ssa/ssa_domain.h"
#include "../ssa/guard_domain.h"
#include "../ssa/function_ssa.h"
#include "index.h"
#include "ssa_data_flow.h"

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
  ssa_ait ssa_analysis;
  ssa_analysis(goto_function);
  ssa_analysis.output(ns, goto_function.body, out);
}

/*******************************************************************\

Function: show_defs

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void show_defs(
  const indext &index,
  const optionst &options,
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
    
    // add the properties
    goto_check(options, model);
    model.goto_functions.update();
    label_properties(model.goto_functions);

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

/*******************************************************************\

Function: show_guards

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void show_guards(
  const goto_functionst::goto_functiont &goto_function,
  const namespacet &ns,
  std::ostream &out)
{
  guard_ait guard_ai;
  guard_ai(goto_function);
  guard_ai.output(ns, goto_function.body, out);
}

/*******************************************************************\

Function: show_guards

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void show_guards(
  const indext &index,
  const optionst &options,
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
    
    // add the properties
    goto_check(options, model);
    model.goto_functions.update();
    label_properties(model.goto_functions);

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
          
      show_guards(*index_fkt, ns, out);
      
      out << std::endl;
    }
  }
  
}

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
  const optionst &options,
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
    
    // add the properties
    goto_check(options, model);
    model.goto_functions.update();
    label_properties(model.goto_functions);

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
          
      show_ssa(*index_fkt, ns, out);
      
      out << std::endl;
    }
  }
  
}

/*******************************************************************\

Function: show_fixed_point

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void show_fixed_point(
  const goto_functionst::goto_functiont &goto_function,
  const namespacet &ns,
  std::ostream &out)
{
  function_SSAt function_SSA(goto_function, ns);
  ssa_data_flowt ssa_data_flow(function_SSA, ns);
  ssa_data_flow.print_invariant(out);
}

/*******************************************************************\

Function: show_fixed_points

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void show_fixed_points(
  const indext &index,
  const optionst &options,
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
    
    // add the properties
    goto_check(options, model);
    model.goto_functions.update();
    label_properties(model.goto_functions);

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
          
      show_fixed_point(*index_fkt, ns, out);
      
      out << std::endl;
    }
  }
  
}

/*******************************************************************\

Function: show_properties

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void show_properties(
  const indext &index,
  const optionst &options,
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
    
    // add the properties
    goto_check(options, model);
    model.goto_functions.update();
    label_properties(model.goto_functions);
    
    show_properties(model, ui_message_handlert::PLAIN);
  }
  
}
