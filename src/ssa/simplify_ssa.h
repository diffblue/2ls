/*******************************************************************\

Module: SSA Simplification

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// SSA Simplification

#ifndef CPROVER_2LS_SSA_SIMPLIFY_SSA_H
#define CPROVER_2LS_SSA_SIMPLIFY_SSA_H

#include <util/namespace.h>

#include "local_ssa.h"

void simplify(local_SSAt &, const namespacet &);

#endif
