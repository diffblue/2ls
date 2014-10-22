/*******************************************************************\

Module: Incremental Solver Interface

Author: Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_INCREMENTAL_SOLVER_H
#define CPROVER_INCREMENTAL_SOLVER_H 

#include <map>
#include <iostream>

#include <solvers/flattening/bv_pointers.h>
#include <solvers/sat/satcheck.h>

#include "domain.h"
#include "util.h"


//#define DEBUG_FORMULA

class incremental_solvert : public messaget
{

 public:
  typedef std::list<exprt> constraintst;

  explicit incremental_solvert(
    const namespacet &_ns) :
    sat_check(),
    solver(_ns,sat_check), 
    ns(_ns),
    activation_literal_counter(0),
    solver_calls(0)
  { 
  }


  decision_proceduret::resultt operator()()
  {
    solver_calls++;
    return solver();    
  }

  unsigned get_number_of_solver_calls() { return solver_calls; }

  static incremental_solvert *allocate(const namespacet &_ns) 
  { 
    return new incremental_solvert(_ns);
  }

  satcheck_minisat_no_simplifiert sat_check;
  bv_pointerst solver;
  const namespacet &ns;

  literalt new_context();
  void pop_context();
  void make_context_permanent();

  //for debugging
  bvt formula;
  void debug_add_to_formula(const exprt &expr);

  //context assumption literals
  bvt activation_literals;
 protected: 
  unsigned activation_literal_counter;

  //statistics
  unsigned solver_calls;
};

static inline incremental_solvert & operator << (
  incremental_solvert &dest,
  const exprt &src)
{
#if 0
  if(!dest.activation_literals.empty())
    std::cout << "add_to_solver(" << !dest.activation_literals.back() << "): " << from_expr(dest.ns,"",src) << std::endl;
  else
      std::cout << "add_to_solver: " << from_expr(dest.ns,"",src) << std::endl;
#endif
#ifndef DEBUG_FORMULA
  if(!dest.activation_literals.empty())
    dest.solver << or_exprt(src,literal_exprt(!dest.activation_literals.back()));
  else 
    dest.solver << src;
#else
  if(!dest.activation_literals.empty())
    dest.solver << dest.debug_add_to_formula(
      or_exprt(src,literal_exprt(!dest.activation_literals.back())));
  else 
    dest.debug_add_to_formula(src);
#endif
  return dest;
}

static inline incremental_solvert& operator << (
  incremental_solvert &dest,
  const incremental_solvert::constraintst &src)
{
    for(incremental_solvert::constraintst::const_iterator it = src.begin(); 
        it != src.end(); it++)
    {
#ifndef DEBUG_FORMULA
      dest.solver << *it;
#else
      dest.debug_add_to_formula(*it);
#endif
    }
  return dest;
}

#endif
