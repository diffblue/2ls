/*******************************************************************\

Module: Summarizer for Nontermination Bit-level analysis

Author: Stefan Marticek

\*******************************************************************/

#include <iostream>

#include "summary_checker_nonterm.h"

#include <util/i2string.h>
#include <util/simplify_expr.h>
#include <util/prefix.h>

#include <ssa/simplify_ssa.h>
#include <ssa/ssa_var_collector.h>

property_checkert::resultt summary_checker_nontermt::operator()(
  const goto_modelt &goto_model)
{
  const namespacet ns(goto_model.symbol_table);

  SSA_functions(goto_model, ns);
  ssa_dbt::functionst& funcs=ssa_db.functions();

  property_checkert::resultt result=property_checkert::UNKNOWN;

  ssa_unwinder.init(false, false);  //is_kinduction, is_bmc - HOW TO SET IT?
  //--k-induction, --incremental-bmc, unwinding?
  ssa_unwinder.init_localunwinders();
  ssa_unwinder.unwind_all(0);

  //unsigned max_unwind = 10;
  for (auto f_ssa_it=funcs.begin(); f_ssa_it!=funcs.end(); ++f_ssa_it)
  {
    local_SSAt &SSA=ssa_db.get(f_ssa_it->first);
    ssa_local_unwindert &ssa_lu=ssa_unwinder.get(f_ssa_it->first);
    ssa_var_collectort ssa_vc=ssa_var_collectort(options, ssa_lu);

    //TODO: replace std::cout with debug()

    std::cout << "\n\n**********>> " << id2string(f_ssa_it->first) << " <<**************\n\n";

    ssa_vc.collect_variables_loop(SSA, true, ns);

    std::cout << "\n\n**********>> " << id2string(f_ssa_it->first) << " <<**************\n\n";

    SSA.output(std::cout);
  }

  return result;
}
