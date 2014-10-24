#include <iostream>
#include <set>
#include <cmath>

#include <solvers/flattening/bv_pointers.h>
#include <util/i2string.h>

#include "incremental_solver.h"

literalt incremental_solvert::new_context() 
{
  literalt activation_literal = solver.convert(
      symbol_exprt("goto_symex::\\act$"+
      i2string(activation_literal_counter++), bool_typet()));

#ifdef DEBUG_OUTPUT
    debug() << "new context: " << activation_literal<< eom;
#endif

  activation_literals.push_back(activation_literal);
  solver.set_assumptions(activation_literals);
  return !activation_literals.back();
}

void incremental_solvert::pop_context() 
{
  assert(!activation_literals.empty());
  literalt activation_literal = activation_literals.back();
  activation_literals.pop_back();
#ifndef DEBUG_FORMULA
  solver.set_to_false(literal_exprt(activation_literal));
#else
  formula.push_back(!activation_literal);
#endif

#ifdef DEBUG_OUTPUT
    debug() << "pop context: " << activation_literal<< eom;
#endif

  solver.set_assumptions(activation_literals);
}

void incremental_solvert::make_context_permanent() 
{
  assert(!activation_literals.empty());
  literalt activation_literal = activation_literals.back();
  activation_literals.pop_back();
#ifndef DEBUG_FORMULA
  solver.set_to_true(literal_exprt(activation_literal));
#else
  formula.push_back(activation_literal);
#endif

#ifdef DEBUG_OUTPUT
    debug() << "make context permanent: " << activation_literal<< eom;
#endif

  solver.set_assumptions(activation_literals);
}

void incremental_solvert::debug_add_to_formula(const exprt &expr) 
{
  literalt l = solver.convert(expr);
  if(l.is_false())
  {
#ifdef DEBUG_OUTPUT
    debug() << "literal " << l << ": false = " << from_expr(ns,"",expr) <<eom;
#endif
    literalt dummy = solver.convert(symbol_exprt("goto_symex::\\dummy", 
						 bool_typet()));
    formula.push_back(dummy);
    formula.push_back(!dummy);
#ifdef DEBUG_OUTPUT
    debug() << "literal " << dummy << ", " << !dummy << ": " 
	      << from_expr(ns,"",expr) << eom;
#endif
  }
  else if(!l.is_true()) 
  {
#ifdef DEBUG_OUTPUT
    debug() << "literal " << l << ": " << from_expr(ns,"",expr) << eom;
#endif
    formula.push_back(l);
  }
}
