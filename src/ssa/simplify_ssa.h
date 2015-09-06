/*******************************************************************\

Module: SSA Simplification

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SIMPLIFY_SSA_H
#define CPROVER_SIMPLIFY_SSA_H

#include <util/namespace.h>

#include "local_ssa.h"

void simplify(local_SSAt &, const namespacet &);

#endif
