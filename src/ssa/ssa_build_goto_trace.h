/*******************************************************************\

Module: Traces of GOTO Programs for SSA Models

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_SSA_BUILD_GOTO_TRACE_H
#define CPROVER_SSA_BUILD_GOTO_TRACE_H

#include <goto-programs/goto_trace.h>
#include <solvers/prop/prop_conv.h>

#include "local_ssa.h"

class ssa_build_goto_tracet {
public:
  ssa_build_goto_tracet() {}

  void operator()(
    const local_SSAt &,
    const prop_convt &,
    goto_tracet &);

protected:
  exprt finalize_lhs(
    const exprt &src,
    const local_SSAt &local_SSA,
    const prop_convt &prop_conv,
    goto_programt::const_targett current_pc);

  void record_step(
    const local_SSAt &local_SSA,
    const prop_convt &prop_conv,
    goto_programt::const_targett current_pc,
    goto_tracet &goto_trace,
    unsigned &step_nr);
};

#endif
