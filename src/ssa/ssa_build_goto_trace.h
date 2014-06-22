/*******************************************************************\

Module: Traces of GOTO Programs for SSA Models

Author: Daniel Kroening

Date: June 2014

\*******************************************************************/

#ifndef CPROVER_SSA_BUILD_GOTO_TRACE_H
#define CPROVER_SSA_BUILD_GOTO_TRACE_H

#include <goto-programs/goto_trace.h>
#include <solvers/prop/prop_conv.h>

#include "local_ssa.h"

void build_goto_trace(
  const local_SSAt &,
  const prop_convt &,
  goto_tracet &);

#endif
