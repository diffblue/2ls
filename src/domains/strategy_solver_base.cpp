#include <iostream>
#include <set>
#include <cmath>

#include <solvers/flattening/bv_pointers.h>
#include <util/i2string.h>

#include "strategy_solver_base.h"

literalt strategy_solver_baset::new_context() 
{
  literalt activation_literal = solver.convert(
      symbol_exprt("goto_symex::\\act$"+
      i2string(activation_literal_counter++), bool_typet()));

#if 0
    debug() << "new context: " << activation_literal<< eom;
#endif

  activation_literals.push_back(activation_literal);
  solver.set_assumptions(activation_literals);
  return !activation_literals.back();
}

void strategy_solver_baset::pop_context() 
{
  assert(!activation_literals.empty());
  literalt activation_literal = activation_literals.back();
  activation_literals.pop_back();
#ifndef DEBUG_FORMULA
  solver.set_to_false(literal_exprt(activation_literal));
#else
  formula.push_back(!activation_literal);
#endif

#if 0
    debug() << "pop context: " << activation_literal<< eom;
#endif

  solver.set_assumptions(activation_literals);
}

void strategy_solver_baset::make_context_permanent() 
{
  assert(!activation_literals.empty());
  literalt activation_literal = activation_literals.back();
  activation_literals.pop_back();
#ifndef DEBUG_FORMULA
  solver.set_to_true(literal_exprt(activation_literal));
#else
  formula.push_back(activation_literal);
#endif

#if 0
    debug() << "make context permanent: " << activation_literal<< eom;
#endif

  solver.set_assumptions(activation_literals);
}

void strategy_solver_baset::debug_add_to_formula(const exprt &expr) 
{
  literalt l = solver.convert(expr);
  if(l.is_false())
  {
    literalt dummy = solver.convert(symbol_exprt("goto_symex::\\dummy", bool_typet()));
    formula.push_back(dummy);
    formula.push_back(!dummy);
    std::cout << "literal " << dummy << ", " << !dummy << ": " << from_expr(ns,"",expr) << std::endl;
  }
  else if(!l.is_true()) 
  {
    std::cout << "literal " << l << ": " << from_expr(ns,"",expr) << std::endl;
    formula.push_back(l);
  }
}
