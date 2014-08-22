/*******************************************************************\

Module: SSA for malloc()

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_MALLOC_SSA_H
#define CPROVER_MALLOC_SSA_H

#include <util/std_code.h>

exprt malloc_ssa(
  const side_effect_exprt &,
  const std::string &suffix,
  const namespacet &);

#endif
