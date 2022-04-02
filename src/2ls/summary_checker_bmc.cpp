/*******************************************************************\

Module: Summary Checker for BMC

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Summary Checker for BMC

#include <ssa/unwinder.h>
#include "summary_checker_bmc.h"


resultt summary_checker_bmct::operator()(
  const goto_modelt &goto_model)
{
  SSA_functions(goto_model, goto_model.symbol_table);

  ssa_unwinder->init(unwinder_modet::BMC);

  resultt result=resultt::UNKNOWN;
  unsigned max_unwind=options.get_unsigned_int_option("unwind");
  status() << "Max-unwind is " << max_unwind << eom;
  ssa_unwinder->init_localunwinders();

  for(unsigned unwind=0; unwind<=max_unwind; unwind++)
  {
    status() << "Unwinding (k=" << unwind << ")" << messaget::eom;
    summary_db.mark_recompute_all();
    ssa_unwinder->unwind_all(unwind);
    result=check_properties();
    if(result==resultt::PASS)
    {
      status() << "incremental BMC proof found after "
         << unwind << " unwinding(s)" << messaget::eom;
      break;
    }
    else if(result==resultt::FAIL)
    {
      status() << "incremental BMC counterexample found after "
         << unwind << " unwinding(s)" << messaget::eom;
      break;
    }
  }
  report_statistics();
  return result;
}
