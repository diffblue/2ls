#ifndef CPROVER_STRATEGY_SOLVER_BASE_H
#define CPROVER_STRATEGY_SOLVER_BASE_H 

#include <map>
#include <iostream>

#include <util/replace_expr.h>
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
    replace_mapt &_renaming_map,
    bv_pointerst &_solver, 
    const namespacet &_ns) :
    renaming_map(_renaming_map),
    solver(_solver), 
    ns(_ns),
    activation_literal_counter(0)
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

 protected: 
  replace_mapt &renaming_map;
  
  inline void rename(exprt &expr) { replace_expr(renaming_map, expr); }
  inline void rename(exprt::operandst &operands)
  {
    for(unsigned i=0; i<operands.size(); ++i)
      replace_expr(renaming_map, operands[i]);
  }

  bv_pointerst &solver;
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

};

#endif
