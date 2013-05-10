/*******************************************************************\

Module: Summarization

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "summarize_function_pointers.h"

/*******************************************************************\

Function: summarize_function_pointers

  Inputs:

 Outputs:

 Purpose: field-sensitive value-set analysis for function pointers

\*******************************************************************/

void summarize_function_pointers(
  const contextt &context,
  const goto_programt::instructiont &instruction,
  function_pointerst &function_pointers)
{
  if(instruction.is_assign())
  {
    
  }
}

/*******************************************************************\

Function: summarize_function_pointers

  Inputs:

 Outputs:

 Purpose: field-sensitive value-set analysis for function pointers

\*******************************************************************/

void summarize_function_pointers(
  const contextt &context,
  const goto_programt &goto_program,
  function_pointerst &function_pointers)
{
  forall_goto_program_instructions(i_it, goto_program)
  {
    summarize_function_pointers(context, *i_it, function_pointers);
  }
}

/*******************************************************************\

Function: summarize_function_pointers

  Inputs:

 Outputs:

 Purpose: field-sensitive value-set analysis for function pointers

\*******************************************************************/

void summarize_function_pointers(
  const contextt &context,
  const goto_functionst &goto_functions,
  function_pointerst &function_pointers)
{
  forall_goto_functions(f_it, goto_functions)
  {
    summarize_function_pointers(context, f_it->second.body, function_pointers);
  }
}

