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
#include "../ssa/guard_map.h"
#include "../ssa/local_ssa.h"
#include "../functions/index.h"
#include "ssa_fixed_point.h"

#include "../ai/summarizer.h"
#include "../ai/summary_store.h"

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
  assignmentst assignments(goto_function.body, ns);
  ssa_ait ssa_analysis(assignments);
  ssa_analysis(goto_function, ns);
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
    read_goto_binary(index.full_path(file_it->first), model, message_handler);
    
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
      
      const goto_functionst::function_mapt::const_iterator m_it=
        model.goto_functions.function_map.find(id);
        
      assert(m_it!=model.goto_functions.function_map.end());
      
      const goto_functionst::goto_functiont *index_fkt=
        &m_it->second;
    
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
  guard_mapt guard_map(goto_function.body);
  guard_map.output(goto_function.body, out);
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
    read_goto_binary(index.full_path(file_it->first), model, message_handler);
    
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

      const goto_functionst::function_mapt::const_iterator m_it=
        model.goto_functions.function_map.find(id);
        
      assert(m_it!=model.goto_functions.function_map.end());
      
      const goto_functionst::goto_functiont *index_fkt=
        &m_it->second;
    
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
  local_SSAt local_SSA(goto_function, ns);
  local_SSA.assertions_to_constraints();
  local_SSA.output(out);
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
#if 1
  summary_storet summary_store;
  summarizert summarizer(summary_store);
#endif

  for(indext::file_to_functiont::const_iterator
      file_it=index.file_to_function.begin();
      file_it!=index.file_to_function.end();
      file_it++)
  {
    // read the file
    goto_modelt model;
    read_goto_binary(index.full_path(file_it->first), model, message_handler);
    
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

      const goto_functionst::function_mapt::const_iterator m_it=
        model.goto_functions.function_map.find(id);
        
      assert(m_it!=model.goto_functions.function_map.end());
      
      const goto_functionst::goto_functiont *index_fkt=
        &m_it->second;
    
      out << ">>>> Function " << id << " in " << file_it->first
          << std::endl;
          
      goto_functionst::goto_functiont fct = *index_fkt;
      preprocess_returns(fct);
      show_ssa(fct, ns, out);

#if 0
     //call summarizer per function
      local_SSAt local_SSA(fct, ns);
      local_SSA.assertions_to_constraints();
      summaryt summary = summarizer.summarize(
      summarizert::functiont(id,&local_SSA));
      summary.output(out,ns);
#endif
      
      out << std::endl;
    }

#if 1
     //call summarizer per module
    summarizert::functionst sfunctions;
    for(std::set<irep_idt>::const_iterator fkt_it=functions.begin();
        fkt_it!=functions.end(); fkt_it++)
    {
      const goto_functionst::function_mapt::const_iterator m_it=
        model.goto_functions.function_map.find(*fkt_it);
      goto_functionst::goto_functiont fct = m_it->second;
      preprocess_returns(fct);
      local_SSAt* local_SSA = new local_SSAt(fct, ns);
      local_SSA->assertions_to_constraints();
      sfunctions[*fkt_it] = local_SSA;
    }
    summarizer.summarize(sfunctions);
    for(std::set<irep_idt>::const_iterator fkt_it=functions.begin();
        fkt_it!=functions.end(); fkt_it++)
    {
      out << ">>>> Summary for " << *fkt_it << std::endl;
      summary_store.get(*fkt_it).output(out,ns);
      out <<  std::endl;
    }
#endif
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
  local_SSAt local_SSA(goto_function, ns);
  ssa_fixed_pointt ssa_fixed_point(local_SSA, ns);
  ssa_fixed_point.output(out);
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
    read_goto_binary(index.full_path(file_it->first), model, message_handler);
    
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

      const goto_functionst::function_mapt::const_iterator m_it=
        model.goto_functions.function_map.find(id);
        
      assert(m_it!=model.goto_functions.function_map.end());
      
      const goto_functionst::goto_functiont *index_fkt=
        &m_it->second;
    
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
    read_goto_binary(index.full_path(file_it->first), model, message_handler);
    
    // add the properties
    goto_check(options, model);
    model.goto_functions.update();
    label_properties(model.goto_functions);
    
    show_properties(model, ui_message_handlert::PLAIN);
  }
  
}
