#include <util/std_expr.h>
#include <util/symbol_table.h>

#include "split_loopheads.h"

/*******************************************************************\

Function: split_loopheads

Inputs:

Outputs:

Purpose: insert skip at jump targets if they are goto or assume instructions

\*******************************************************************/

void split_loopheads(goto_modelt &goto_model)
{
  Forall_goto_functions(f_it, goto_model.goto_functions)
  {
    Forall_goto_program_instructions(i_it, f_it->second.body)
    {
      if(!i_it->is_backwards_goto()) continue;
      if(i_it->guard.is_true()) continue;
      goto_programt::targett loophead = i_it->get_target();
      if(!loophead->is_goto() && !loophead->is_assume()) continue;
      
      // inserts the skip
      goto_programt::targett new_loophead = 
	f_it->second.body.insert_before(loophead);
      new_loophead->make_skip();
      new_loophead->source_location=loophead->source_location;
      new_loophead->function=i_it->function;

      // update jumps to loophead
      for(std::set<goto_programt::targett>::iterator j_it = loophead->incoming_edges.begin();
	  j_it != loophead->incoming_edges.end(); j_it++)
      {
	(*j_it)->targets.clear();
	(*j_it)->targets.push_back(new_loophead);
      }
    }
  }
}
