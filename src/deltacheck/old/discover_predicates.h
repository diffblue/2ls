/*******************************************************************\

Module: Predicate Discovery

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <list>

#include <util/namespace.h>
#include <util/expr.h>

std::list<exprt> discover_predicates(
  const exprt &src,
  const namespacet &ns);
