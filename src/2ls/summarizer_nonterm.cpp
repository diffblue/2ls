/*******************************************************************\

Module: Summarizer for Nontermination Bit-level analysis

Author: Stefan Marticek

\*******************************************************************/

#include <iostream>

#include "summarizer_nonterm.h"

#include <util/i2string.h>
#include <util/simplify_expr.h>
#include <util/prefix.h>

#include <ssa/simplify_ssa.h>
#include <ssa/ssa_var_collector.h>

void summarizer_nonterm::check_nontermination(const goto_modelt &goto_model)
{
  const namespacet ns(goto_model.symbol_table);
  ssa_dbt::functionst& funcs=ssa_db.functions();

  forall_goto_functions(f_it, goto_model.goto_functions)
  {
    if(!f_it->second.body_available())
      continue;
    if(has_prefix(id2string(f_it->first), TEMPLATE_DECL))
      continue;
    status() << "Computing SSA of " << f_it->first << messaget::eom;

    ssa_db.create(f_it->first, f_it->second, ns);
    local_SSAt &SSA=ssa_db.get(f_it->first);
    
    ssa_local_unwindert ssa_lu = ssa_local_unwindert(f_it->first, *funcs[f_it->first], false, true);
    ssa_var_collectort ssa_vc = ssa_var_collectort(options, ssa_lu);
    
    std::cout << "\n\n**********>> " << id2string(f_it->first) << " <<**************\n\n";
    
    ssa_vc.collect_variables_loop(SSA, true, ns);
    
    std::cout << "\n\n**********>> " << id2string(f_it->first) << " <<**************\n\n";

    // simplify, if requested
    if(false)
    {
      status() << "Simplifying" << messaget::eom;
      ::simplify(SSA, ns);
    }

    SSA.output(std::cout); std::cout << eom;
  }
}

void summarizer_nonterm::check_nontermination_refactor(const goto_modelt &goto_model)
{
  const namespacet ns(goto_model.symbol_table);

  SSA_functions(goto_model, ns);
  ssa_dbt::functionst& funcs=ssa_db.functions();

  ssa_unwinder.init(false, false);  //is_kinduction, is_bmc - HOW TO SET IT?
  //--k-induction, --incremental-bmc, unwinding?
  ssa_unwinder.init_localunwinders();
  ssa_unwinder.unwind_all(10);

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
}
