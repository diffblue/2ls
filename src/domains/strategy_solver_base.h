#ifndef CPROVER_STRATEGY_SOLVER_BASE_H
#define CPROVER_STRATEGY_SOLVER_BASE_H 

#include <map>
#include <iostream>

#include <solvers/flattening/bv_pointers.h>

#include "domain.h"

//#define DEBUG_FORMULA

class strategy_solver_baset : public messaget
{

 public:
  typedef std::list<exprt> constraintst;
  typedef std::vector<symbol_exprt> var_listt;
  typedef domaint::valuet invariantt;

  explicit strategy_solver_baset(
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

  virtual bool iterate(invariantt &inv) { assert(false); }

  unsigned get_number_of_solver_calls() { return solver_calls; }

 protected: 
  bv_pointerst &solver;

  inline decision_proceduret::resultt solve() {
    solver_calls++;
    return solver();    
  }

  const namespacet &ns;

  //handles on values to retrieve from model
  bvt strategy_cond_literals;
  exprt::operandst strategy_value_exprs;

  //context assumption literals
  bvt activation_literals;
  unsigned activation_literal_counter;
  literalt new_context();
  void pop_context();
  void make_context_permanent();
  bvt formula;

  //statistics
  unsigned solver_calls;
};

#endif
