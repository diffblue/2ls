/*******************************************************************\

Module: Predicate Discovery

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <list>

#include <namespace.h>
#include <expr.h>

std::list<exprt> discover_predicates(
  const exprt &src,
  const namespacet &ns);
