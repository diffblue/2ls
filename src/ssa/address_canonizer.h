/*******************************************************************\

Module: Canonize addresses of objects

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_ADDRESS_CANONIZER_H
#define CPROVER_ADDRESS_CANONIZER_H

#include <util/namespace.h>
#include <util/expr.h>

exprt address_canonizer(
  const exprt &address,
  const namespacet &ns);

#endif
