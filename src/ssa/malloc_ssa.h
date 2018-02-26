/*******************************************************************\

Module: SSA for malloc()

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_2LS_SSA_MALLOC_SSA_H
#define CPROVER_2LS_SSA_MALLOC_SSA_H

#include <util/std_code.h>
#include <goto-programs/goto_model.h>

exprt malloc_ssa(
  const side_effect_exprt &,
  const std::string &suffix,
  symbol_tablet &);

bool replace_malloc(
  goto_modelt &goto_model,
  const std::string &suffix);

void allow_record_malloc(goto_modelt &goto_model);
void allow_record_memleak(goto_modelt &goto_model);

#endif
