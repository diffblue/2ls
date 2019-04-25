/*******************************************************************\

Module: Canonize addresses of objects

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Canonize addresses of objects

#ifndef CPROVER_2LS_SSA_ADDRESS_CANONIZER_H
#define CPROVER_2LS_SSA_ADDRESS_CANONIZER_H

#include <util/namespace.h>
#include <util/expr.h>

exprt address_canonizer(
  const exprt &address,
  const namespacet &ns);

#endif
