/*******************************************************************\

Module: Summary Checker for BMC

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Summary Checker for BMC

#include "summary_checker_bmc.h"


property_checkert::resultt summary_checker_bmct::operator()(
  const goto_modelt &goto_model)
{
  const namespacet ns(goto_model.symbol_table);

  SSA_functions(goto_model, ns, heap_analysis);

  ssa_unwinder.init(false, true);

  property_checkert::resultt result=property_checkert::UNKNOWN;
  unsigned max_unwind=options.get_unsigned_int_option("unwind");
  status() << "Max-unwind is " << max_unwind << eom;
  ssa_unwinder.init_localunwinders();

  for(unsigned unwind=0; unwind<=max_unwind; unwind++)
  {
    status() << "Unwinding (k=" << unwind << ")" << messaget::eom;
    summary_db.mark_recompute_all();
    ssa_unwinder.unwind_all(unwind);
    result=check_properties();
    if(result==property_checkert::PASS)
    {
      status() << "incremental BMC proof found after "
         << unwind << " unwinding(s)" << messaget::eom;
      break;
    }
    else if(result==property_checkert::FAIL)
    {
      status() << "incremental BMC counterexample found after "
         << unwind << " unwinding(s)" << messaget::eom;
      break;
    }
  }
  report_statistics();
  return result;
}
