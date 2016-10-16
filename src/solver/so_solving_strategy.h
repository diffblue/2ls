/*******************************************************************\

Module: Strategy for solving a second order formula

Author: Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_2LS_SO_SOLVING_STRATEGY_H
#define CPROVER_2LS_SO_SOLVING_STRATEGY_H

#include "so_formula.h"

class so_solving_strategyt
{
public:
  so_solving_strategyt(
    const so_formula &_sof,
    const namespacet &_ns)
    : sof(_sof), ns(_ns)
  {
  }

protected:
  const so_formula &sof;
  const namespacet &ns;

// TODO: map predicates to domains
//  typedef std::map<predicatet, dom_spect> dom_mapt;
//  dom_mapt dom_map;

};

#endif
