/*******************************************************************\

Module: Summary Checker for k-induction

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Summary Checker for k-induction

#include <ssa/unwinder.h>

#include "summary_checker_kind.h"

resultt summary_checker_kindt::operator()()
{
  SSA_functions(goto_model, goto_model.symbol_table);

  ssa_unwinder->init(unwinder_modet::K_INDUCTION);

  resultt result=resultt::UNKNOWN;
  unsigned max_unwind=options.get_unsigned_int_option("unwind");
  unsigned give_up_invariants=
    options.get_unsigned_int_option("give-up-invariants");
  status() << "Max-unwind is " << max_unwind << eom;
  ssa_unwinder->init_localunwinders();

  for(unsigned unwind=0; unwind<=max_unwind; unwind++)
  {
    status() << "Unwinding (k=" << unwind << ")" << eom;

    // TODO: recompute only functions with loops
    summary_db.mark_recompute_all();

    ssa_unwinder->unwind_all(unwind);

    result=check_properties();
    bool magic_limit_not_reached=
      unwind<give_up_invariants ||
      !options.get_bool_option("competition-mode");
    if(result==resultt::UNKNOWN && !options.get_bool_option("havoc") &&
       magic_limit_not_reached)
    {
      summarize(goto_model);
      result=check_properties();
    }

    if(result==resultt::PASS)
    {
      status() << "k-induction proof found after "
         << unwind << " unwinding(s)" << eom;
      break;
    }
    else if(result==resultt::FAIL)
    {
      status() << "k-induction counterexample found after "
         << unwind << " unwinding(s)" << eom;
      break;
    }
  }
  report_statistics();
  return result;
}

