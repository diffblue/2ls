/*******************************************************************\

Module: Incremental Solver Interface

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Incremental Solver Interface

#ifdef DEBUG
#include <iostream>
#endif

#include <set>

#include <solvers/flattening/bv_pointers.h>

#include "incremental_solver.h"

void incremental_solvert::new_context()
{
#ifdef NON_INCREMENTAL
  contexts.push_back(constraintst());

#if 0
  std::cerr << "new context: " << contexts.size() << std::endl;
#endif

#else
  solver->push();
#ifdef DEBUG_OUTPUT
    debug() << "new context" <<  eom;
#endif
#endif
}

void incremental_solvert::pop_context()
{
#ifdef NON_INCREMENTAL
  assert(!contexts.empty());

#if 0
  std::cerr << "pop context: " << contexts.size() << std::endl;
#endif

  contexts.pop_back();

#else

  solver->pop();
#ifdef DEBUG_OUTPUT
    debug() << "pop context" << eom;
#endif
#endif
}

void incremental_solvert::debug_add_to_formula(const exprt &expr)
{
#ifdef NON_INCREMENTAL
  // no debug mode for non-incremental yet
#else
  literalt l=solver->convert(expr);
  if(l.is_false())
  {
#ifdef DEBUG_OUTPUT
    debug() << "literal " << l << ": false=" << from_expr(ns, "", expr) <<eom;
#endif
    literalt dummy=
      solver->convert(symbol_exprt("goto_symex::\\dummy", bool_typet()));
    formula.push_back(dummy);
    formula.push_back(!dummy);
#ifdef DEBUG_OUTPUT
    debug() << "literal " << dummy << ", " << !dummy << ": "
        << from_expr(ns, "", expr) << eom;
#endif
  }
  else if(!l.is_true())
  {
#ifdef DEBUG_OUTPUT
    debug() << "literal " << l << ": " << from_expr(ns, "", expr) << eom;
#endif
    formula.push_back(l);
  }
#endif
}
