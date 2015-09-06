/*******************************************************************\

Module: Change Impact

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <stack>

#include <goto-programs/read_goto_binary.h>
#include <goto-programs/goto_model.h>

#include "call_graph.h"
#include "get_function.h"

/*******************************************************************\

Function: call_grapht::build

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void call_grapht::build(
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
