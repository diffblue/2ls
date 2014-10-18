#ifndef CPROVER_INCREMENTAL_SOLVER_H
#define CPROVER_INCREMENTAL_SOLVER_H 

#include <map>
#include <iostream>

#include <solvers/flattening/bv_pointers.h>

#include "domain.h"
#include "util.h"


//#define DEBUG_FORMULA

class incremental_solvert : public messaget
{

 public:
  typedef std::list<exprt> constraintst;

  explicit incremental_solvert(
    const constraintst &program,
    bv_pointerst &_solver, 
    const namespacet &_ns) :
    solver(_solver), 
    ns(_ns),
    activation_literal_counter(0),
    solver_calls(0)
  { 
    // adding program constraints to solver db
    for(constraintst::const_iterator it = program.begin(); 
        it != program.end(); it++)
    {

#ifndef DEBUG_FORMULA
#if 0
      std::cout << "program: " << from_expr(ns,"",*it) << std::endl;
#endif
      solver << *it;
#else
      literalt l = solver.convert(*it);
      if(!l.is_constant()) 
      {
	std::cout << "literal " << l << ": " << from_expr(ns,"",*it) 
          << std::endl;
        formula.push_back(l);
      }
#endif
    }
}

  decision_proceduret::resultt solve() 
  {
    solver_calls++;
    return solver();    
  }

  unsigned get_number_of_solver_calls() { return solver_calls; }

 protected: 
  bv_pointerst &solver;
  const namespacet &ns;

  //context assumption literals
  bvt activation_literals;
  unsigned activation_literal_counter;
  literalt new_context();
  void pop_context();
  void make_context_permanent();

  //for debugging
  bvt formula;
  void debug_add_to_formula(const exprt &expr);

  //statistics
  unsigned solver_calls;
};

#endif
