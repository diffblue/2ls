/*******************************************************************\

Module: Partial Canonicalization of a Predicate

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_CEGAR_CANONICALIZE_H
#define CPROVER_CEGAR_CANONICALIZE_H

class exprt;
class namespacet;

void canonicalize(exprt &expr, bool &negation, const namespacet &ns);
void canonicalize(exprt &expr, const namespacet &ns);

#endif
