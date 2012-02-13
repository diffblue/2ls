/*******************************************************************\

Module: Summarization

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "summarization.h"
#include "summarize_function_pointers.h"

/*******************************************************************\

Function: summarization

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarization(
  const std::string &file_name,
  const contextt &context,
  const goto_functionst &goto_functions,
  const optionst &options)
{
  function_pointerst function_pointers;
  
  summarize_function_pointers(context, goto_functions, function_pointers);
}
