/*******************************************************************\

Module: Strategy for solving a second-order formula

Author: Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_2LS_SO_SOLVING_STRATEGY_H
#define CPROVER_2LS_SO_SOLVING_STRATEGY_H

#include <ssa/ssa_db.h>

#include "so_formula.h"
#include "predicate.h"

class so_solving_strategyt
{
public:
  so_solving_strategyt(
    const so_formulat &_sof,
    const ssa_dbt &_ssa_db,
    const namespacet &_ns)
    : sof(_sof), ssa_db(_ssa_db), ns(_ns)
  {
  }

  typedef std::map<predicate_symbol_exprt, exprt> predicate_bindingst;

  const so_formulat &sof;
  const ssa_dbt &ssa_db;
  const namespacet &ns;
protected:

// TODO: map predicates to domains
//  typedef std::map<predicatet, dom_spect> dom_mapt;
//  dom_mapt dom_map;

};

#endif
