/*******************************************************************\

Module: Data Flow Analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef DELTACHECK_SSA_FIXED_POINT_H
#define DELTACHECK_SSA_FIXED_POINT_H

#include "../ssa/local_ssa.h"

void ssa_fixed_point(local_SSAt &, const namespacet &);

#endif
