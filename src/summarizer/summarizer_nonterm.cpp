/*******************************************************************\

Module: Summarizer for Nontermination Bit-level analysis

Author: Stefan Marticek

\*******************************************************************/

#include <iostream>

#include "summarizer_nonterm.h"

#include "../ssa/ssa_var_collector.h"

#include <ssa/ssa_db.h>

void summarizer_nonterm::check_nontermination(const goto_modelt & goto_model)
{
    const namespacet ns(goto_model.symbol_table);
    
    forall_goto_functions(f_it, goto_model.goto_functions)
  {
    if(!f_it->second.body_available())
      continue;
    if(has_prefix(id2string(f_it->first), TEMPLATE_DECL))
      continue;
    status() << "Computing SSA of " << f_it->first << messaget::eom;

    ssa_db.create(f_it->first, f_it->second, ns);
    local_SSAt &SSA=ssa_db.get(f_it->first);

    // simplify, if requested
    if(true)
    {
      status() << "Simplifying" << messaget::eom;
      ::simplify(SSA, ns);
    }

    SSA.output(debug()); debug() << eom;
  }
    //std::cout << "\n\n**********Second run**************\n\n";
}