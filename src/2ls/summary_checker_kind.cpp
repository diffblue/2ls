/*******************************************************************\

Module: Summary Checker for k-induction

Author: Peter Schrammel

\*******************************************************************/

#include "summary_checker_kind.h"

#define GIVE_UP_INVARIANTS 7

/*******************************************************************\

Function: summary_checker_kindt::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

property_checkert::resultt summary_checker_kindt::operator()(
  const goto_modelt &goto_model)
{
  const namespacet ns(goto_model.symbol_table);

  SSA_functions(goto_model,ns);

  ssa_unwinder.init(true,false);

  property_checkert::resultt result = property_checkert::UNKNOWN;
  unsigned max_unwind = options.get_unsigned_int_option("unwind");
  status() << "Max-unwind is " << max_unwind << eom;
  ssa_unwinder.init_localunwinders();

  for(unsigned unwind = 0; unwind<=max_unwind; unwind++)
  {
    status() << "Unwinding (k=" << unwind << ")" << eom;
    summary_db.mark_recompute_all(); //TODO: recompute only functions with loops
    ssa_unwinder.unwind_all(unwind);

    result =  check_properties(); 
    if(result == property_checkert::UNKNOWN &&
       !options.get_bool_option("havoc") && 
       (unwind<GIVE_UP_INVARIANTS || 
        !options.get_bool_option("competition-mode"))) //magic constant 
    {
      summarize(goto_model);
      result =  check_properties(); 
    }

    if(result == property_checkert::PASS) 
    {
      status() << "k-induction proof found after " 
	       << unwind << " unwinding(s)" << eom;
      break;
    }
    else if(result == property_checkert::FAIL) 
    {
      status() << "k-induction counterexample found after " 
	       << unwind << " unwinding(s)" << eom;
      break;
    }
  }
  report_statistics();
  return result;
}

