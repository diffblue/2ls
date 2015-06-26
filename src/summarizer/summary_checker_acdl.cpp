/*******************************************************************\

Module: Summary Checker using ACDL

Author: Peter Schrammel

\*******************************************************************/

#include "summary_checker_acdl.h"

#include "../acdl/acdl_solver.h"

/*******************************************************************\

Function: summary_checker_acdlt::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

property_checkert::resultt summary_checker_acdlt::operator()(
  const goto_modelt &goto_model)
{
  const namespacet ns(goto_model.symbol_table);

  SSA_functions(goto_model,ns);

  acdl_solvert acdl_solver(options);
  acdl_solver.set_message_handler(get_message_handler());

  property_checkert::resultt result =
    acdl_solver(ssa_db.get(goto_model.goto_functions.entry_point()));
  
  return result;
}


