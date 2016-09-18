/*******************************************************************\

Module: Transformer simplification

Author: Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_SIMPLIFY_TRANSFORMER_H
#define CPROVER_SIMPLIFY_TRANSFORMER_H

#include <set>
#include <util/irep.h>

class exprt;
class namespacet;

//
// simplify transformers by best-effort intermediate variable elimination
//
// true: did nothing
// false: simplified something
//

bool simplify(
  exprt &expr,
  const std::set<irep_idt> &frozen_vars, //do not eliminate these
  const namespacet &ns);

exprt simplify_transformer(
  const exprt &src,
  const std::set<irep_idt> &frozen_vars, //do not eliminate these
  const namespacet &ns);

#endif
