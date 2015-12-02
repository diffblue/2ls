/*******************************************************************\

Module: SSA for malloc()

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_MALLOC_SSA_H
#define CPROVER_MALLOC_SSA_H

#include <util/std_code.h>
#include <goto-programs/goto_model.h>

exprt malloc_ssa(
  const side_effect_exprt &,
  const std::string &suffix,
  symbol_tablet &);


#if 1
void replace_malloc(goto_modelt &goto_model,
		    const std::string &suffix);
#endif

#endif
