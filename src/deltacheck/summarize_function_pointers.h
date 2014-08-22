/*******************************************************************\

Module: Summarization of Function Pointers

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_DELTACHECK_SUMMARIZE_FUNCTION_POINTERS_H
#define CPROVER_DELTACHECK_SUMMARIZE_FUNCTION_POINTERS_H

#include <context.h>
#include <hash_cont.h>

#include <goto-programs/goto_functions.h>

class function_pointerst
{
public:
  // a map from struct.field to a set of function identifiers
  
  typedef std::set<irep_idt> id_sett;

  typedef hash_map_cont<irep_idt, id_sett, irep_id_hash> field_mapt;
  field_mapt field_map;
  
  void print(std::ostream &);
};

void summarize_function_pointers(
  const contextt &,
  const goto_functionst &,
  function_pointerst &dest);

#endif
