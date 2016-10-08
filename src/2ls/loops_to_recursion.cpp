#include "2ls_parse_options.h"

/*******************************************************************\

Function: twols_parse_optionst::loops_to_recursion

  Inputs:

 Outputs:

 Purpose: transforms loops into tail recursion

WHILE/FOR LOOP:

  1: IF c GOTO 2
     loop body
     GOTO 1
  2:

becomes

     IF c GOTO 2
     DECL l_in, l_out
     l_in=locals_read
     l_out=Loop1(l_in)
     locals_written=l_out
     DEAD l_in, l_out
  2:
       
  with Loop1:
     DECL l_out
     locals_read=l_in
     loop body
     IF not c GOTO 2'
     l_in=locals_read
     l_out=Loop1(l_in)
     return l_out
  2':l_out=locals_written
     return l_out
     DEAD l_in, l_out

DO WHILE LOOP:

  1: loop body
     IF c GOTO 1
  2:

becomes

  1: DECL l_in, l_out
     l_in=locals_read
     l_out=Loop1(l_in)
     locals_written=l_out
     DEAD l_in, l_out
  2:
       
  with same form of Loop1
         
\*******************************************************************/

void twols_parse_optionst::loops_to_recursion(goto_modelt &goto_model)
{
  Forall_goto_functions(f_it, goto_model.goto_functions)
  {
    Forall_goto_program_instructions(i_it, f_it->second.body)
    {
      if(!i_it->is_backwards_goto()) continue;
      goto_programt::targett loophead = i_it->get_target();
      bool is_do_while = !i_it->guard.is_true();
      //create function for loop body
      //TODO
      //add DECL for input and output structs
      //TODO
      //add assignments for inputs
      //TODO
      //add function call
      //TODO
      //add assignments for outputs
      //TODO
      //add DEAD for input and output structs
      //TODO
      //remove loop body and backwards goto
      //TODO
    }
  }
}
