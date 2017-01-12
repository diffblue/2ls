/*******************************************************************\

Module: Bounds simplification

Author: Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_2LS_DOMAINS_SIMPLIFY_BOUNDS_H
#define CPROVER_2LS_DOMAINS_SIMPLIFY_BOUNDS_H

#include <set>

class exprt;
class namespacet;

//
// simplify bounds
//
// true: did nothing
// false: simplified something
//

bool simplify_bounds(
  exprt &expr,
  const namespacet &ns);

exprt simplify_bounds(
  const exprt &src,
  const namespacet &ns);

#endif
