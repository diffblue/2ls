/*******************************************************************\

Module: Change Impact

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <stack>

#include <goto-programs/read_goto_binary.h>
#include <goto-programs/goto_model.h>

#include "../functions/get_function.h"
#include "change_impact.h"

/*******************************************************************\

Function: change_impactt::diff

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void change_impactt::diff(
  const indext &old_index,
  const indext &new_index)
{
  for(indext::file_to_functiont::const_iterator
      new_file_it=new_index.file_to_function.begin();
      new_file_it!=new_index.file_to_function.end();
      new_file_it++)
  {
    // read the new file
    goto_modelt new_model;
    read_goto_binary(new_index.full_path(new_file_it), new_model, get_message_handler());

    // do call graph edges
    do_call_graph(new_index, new_file_it->first, new_model);

    function_mapt &functions=file_map[new_file_it->first];

    // is there a corresponding old file?
    indext::file_to_functiont::const_iterator old_file_it=
      old_index.file_to_function.find(new_file_it->first);
    
    if(old_file_it==old_index.file_to_function.end())
    {
      for(goto_functionst::function_mapt::const_iterator
          new_fkt_it=new_model.goto_functions.function_map.begin();
          new_fkt_it!=new_model.goto_functions.function_map.end();
          new_fkt_it++)
      {
        // no corresponding old file, try elsewhere
        get_functiont get_function(old_index);
        
        goto_functionst::goto_functiont *old_fkt=
          get_function(new_fkt_it->first);
          
        if(old_fkt==NULL)
        {
          // old not found, mark as changed
          functions[new_fkt_it->first].fully_changed=true;
        }
        else
          diff_functions(new_file_it->first, new_fkt_it->first, *old_fkt, new_fkt_it->second);
      }
    }
    else
    {
      // read the old file
      goto_modelt old_model;
      read_goto_binary(old_index.full_path(old_file_it), old_model, get_message_handler());
      
      for(goto_functionst::function_mapt::const_iterator
          new_fkt_it=new_model.goto_functions.function_map.begin();
          new_fkt_it!=new_model.goto_functions.function_map.end();
          new_fkt_it++)
      {
        // try to find 'corresponding function' in old_model
        goto_functionst::function_mapt::const_iterator
          old_fkt_it=old_model.goto_functions.function_map.find(new_fkt_it->first);

        if(old_fkt_it==old_model.goto_functions.function_map.end())
          functions[new_fkt_it->first].fully_changed=true;
        else
          diff_functions(new_file_it->first, new_fkt_it->first, old_fkt_it->second, new_fkt_it->second);
      }
    }
  }
}

/*******************************************************************\

Function: change_impactt::diff_functions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void change_impactt::diff_functions(
  const irep_idt &file,
  const irep_idt &function_id,
  const goto_functionst::goto_functiont &old_f,
  const goto_functionst::goto_functiont &new_f)
{
  const goto_programt &old_body=old_f.body;
  const goto_programt &new_body=new_f.body;
  
  // build branch target maps
  
  std::map<unsigned, unsigned> old_target_map;

  forall_goto_program_instructions(it, old_body)
  {
    unsigned nr=old_target_map.size();
    old_target_map[it->location_number]=nr;
  }
  
  std::map<unsigned, unsigned> new_target_map;

  forall_goto_program_instructions(it, new_body)
  {
    unsigned nr=new_target_map.size();
    new_target_map[it->location_number]=nr;
  }
  
  // now diff
  datat &data=file_map[file][function_id];
  
  goto_programt::instructionst::const_iterator
    old_it=old_body.instructions.begin();
  
  forall_goto_program_instructions(new_it, new_body)
  {
    if(new_it->is_skip() ||
       new_it->is_location() ||
       new_it->is_end_function())
      continue;

    while(old_it!=old_body.instructions.end() &&
          (old_it->is_skip() ||
           old_it->is_location() ||
           old_it->is_end_function()))
      old_it++;

    if(new_it->type!=old_it->type ||
       new_it->guard!=old_it->guard ||
       new_it->code!=old_it->code ||
       (new_it->is_goto() &&
        new_target_map[new_it->get_target()->location_number]!=
        old_target_map[old_it->get_target()->location_number]))
      data.locs_changed.insert(new_it->location_number);

    old_it++;
  }
}

/*******************************************************************\

Function: change_impactt::output_diff

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void change_impactt::output_diff(std::ostream &out)
{
  for(file_mapt::const_iterator
      file_it=file_map.begin(); file_it!=file_map.end(); file_it++)
  {
    const function_mapt &function_map=file_it->second;
    
    bool change_found=false;
    
    for(function_mapt::const_iterator
        fkt_it=function_map.begin();
        fkt_it!=function_map.end();
        fkt_it++)
      if(fkt_it->second.has_change())
      {
        change_found=true;
        break;
      }
    
    if(!change_found) continue;

    out << "******* File " << file_it->first << "\n";
    
    for(function_mapt::const_iterator
        fkt_it=function_map.begin();
        fkt_it!=function_map.end();
        fkt_it++)
    {
      if(fkt_it->second.fully_changed)
        out << fkt_it->first << ": *\n";
      else if(!fkt_it->second.locs_changed.empty())
      {
        out << fkt_it->first << ":";
        for(std::set<unsigned>::const_iterator
            l_it=fkt_it->second.locs_changed.begin();
            l_it!=fkt_it->second.locs_changed.end();
            l_it++)
          out << " " << *l_it;

        out << "\n";
      }
    }
    
    out << "\n";
  }
}

/*******************************************************************\

Function: change_impactt::output_change_impact

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void change_impactt::output_change_impact(std::ostream &out)
{
  for(file_mapt::const_iterator
      file_it=file_map.begin(); file_it!=file_map.end(); file_it++)
  {
    const function_mapt &function_map=file_it->second;
    
    bool is_affected=false;
    
    for(function_mapt::const_iterator
        fkt_it=function_map.begin();
        fkt_it!=function_map.end();
        fkt_it++)
      if(fkt_it->second.is_affected())
      {
        is_affected=true;
        break;
      }
    
    if(!is_affected) continue;

    out << "******* File " << file_it->first << "\n";
    
    for(function_mapt::const_iterator
        fkt_it=function_map.begin();
        fkt_it!=function_map.end();
        fkt_it++)
    {
      if(fkt_it->second.fully_affected)
        out << fkt_it->first << "\n";
      else if(!fkt_it->second.locs_affected.empty())
      {
        out << fkt_it->first << ":";
        for(std::set<unsigned>::const_iterator
            l_it=fkt_it->second.locs_affected.begin();
            l_it!=fkt_it->second.locs_affected.end();
            l_it++)
          out << " " << *l_it;

        out << "\n";
      }
    }
    
    out << "\n";
  }
}

/*******************************************************************\

Function: change_impactt::change_impact

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void change_impactt::change_impact(const indext &new_index)
{
  std::stack<f_idt> working;
  
  // stash everything with change into the working set
  for(file_mapt::const_iterator
      file_it=file_map.begin();
      file_it!=file_map.end();
      file_it++)
  {
    for(function_mapt::const_iterator
        function_it=file_it->second.begin();
        function_it!=file_it->second.end();
        function_it++)
    {
      if(function_it->second.has_change())
      {
        f_idt f_id;
        f_id.function_id=function_it->first;
        f_id.file=file_it->first;
        working.push(f_id);
      }
    }
  }

  get_functiont get_function(new_index);

  // main loop
  while(!working.empty())
  {
    const f_idt f_id=working.top();
    working.pop();
    
    propagate_affected(new_index, get_function, f_id, working);
  }
}

/*******************************************************************\

Function: change_impactt::propagate_affected

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void change_impactt::propagate_affected(
  const indext &new_index,
  get_functiont &get_function,
  const f_idt &f_id,
  std::stack<f_idt> &working_fkts)
{
  datat &data=file_map[f_id.file][f_id.function_id];

  if(data.fully_affected) return; // done already
  
  // get it
  goto_functionst::goto_functiont *fkt=
    get_function(f_id.function_id);
    
  if(fkt==NULL) return; // give up
  const goto_programt &body=fkt->body;
  if(body.empty()) return; // give up
  
  std::stack<goto_programt::const_targett> working_locs;

  // put anything changed into working_locs  
  forall_goto_program_instructions(l, body)
    if(data.locs_changed.find(l->location_number)!=data.locs_changed.end())
      working_locs.push(l);

  // put anything with an affected function call into working_locs
  forall_goto_program_instructions(l, body)
    if(l->is_function_call())
    {
      const code_function_callt &call=to_code_function_call(l->code);
      if(call.function().id()==ID_symbol)
      {
        const symbol_exprt &symbol=to_symbol_expr(call.function());
        f_idt called_f_id=get_f_id(new_index, f_id.file, symbol.get_identifier());
        if(file_map[called_f_id.file][called_f_id.function_id].is_affected())
          working_locs.push(l);
      }
    }

  while(!working_locs.empty())
  {
    goto_programt::const_targett l=working_locs.top();
    working_locs.pop();
    
    if(data.locs_affected.find(l->location_number)!=data.locs_affected.end())
      continue; // done already

    data.locs_affected.insert(l->location_number);
    
    if(l->is_function_call())
    {
      const code_function_callt &call=to_code_function_call(l->code);
      if(call.function().id()==ID_symbol)
      {
        const symbol_exprt &symbol=to_symbol_expr(call.function());
        f_idt called_f_id=get_f_id(new_index, f_id.file, symbol.get_identifier());
        make_fully_affected(called_f_id);
      }
    }

    goto_programt::const_targetst successors;

    body.get_successors(l, successors);

    for(goto_programt::const_targetst::const_iterator
        it=successors.begin();
        it!=successors.end();
        it++)
    {
      assert(body.instructions.end()!=*it);
      working_locs.push(*it);
    }
  }
}

/*******************************************************************\

Function: change_impactt::make_fully_affected

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void change_impactt::make_fully_affected(const f_idt &f_id)
{
  std::stack<f_idt> working;
  
  working.push(f_id);
  
  while(!working.empty())
  {
    const f_idt f_id=working.top();
    working.pop();
    
    datat &data=file_map[f_id.file][f_id.function_id];
    if(data.fully_affected) continue;
    data.fully_affected=true;

    // recursively make all functions that are called fully affected
    for(std::set<f_idt>::const_iterator
        called_it=data.calls.begin();
        called_it!=data.calls.end();
        called_it++)
    {
      working.push(*called_it);
    }
  }
}

/*******************************************************************\

Function: change_impactt::do_call_graph

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void change_impactt::do_call_graph(
  const indext &index,
  const irep_idt &file,
  const goto_modelt &model)
{
  for(goto_functionst::function_mapt::const_iterator
      new_fkt_it=model.goto_functions.function_map.begin();
      new_fkt_it!=model.goto_functions.function_map.end();
      new_fkt_it++)
  {
    f_idt this_f_id;
    this_f_id.file=file;
    this_f_id.function_id=new_fkt_it->first;
  
    datat &data=file_map[file][new_fkt_it->first];

    const goto_programt &body=new_fkt_it->second.body;
    
    forall_goto_program_instructions(l, body)
      if(l->is_function_call())
      {
        const code_function_callt &call=to_code_function_call(l->code);
        if(call.function().id()==ID_symbol)
        {
          const symbol_exprt &symbol=to_symbol_expr(call.function());
          const f_idt called_f_id=get_f_id(index, file, symbol.get_identifier());
          data.calls.insert(called_f_id);
          file_map[called_f_id.file][called_f_id.function_id].called_by.insert(this_f_id);
        }
      }
  }
}
