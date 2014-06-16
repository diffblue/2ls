#ifndef CPROVER_STRATEGY_SOLVER_BASE
#define CPROVER_STRATEGY_SOLVER_BASE 

#include <util/replace_expr.h>
#include <map>

#include "template_domain.h"

#include <solvers/flattening/bv_pointers.h>


class strategy_solver_baset 
{

 public:
  typedef std::list<exprt> constraintst;
  typedef std::vector<symbol_exprt> var_listt;
  typedef template_domaint::valuet invariantt;
  typedef std::vector<template_domaint::rowt> strategyt;

  explicit strategy_solver_baset(const constraintst &program,
    replace_mapt &_renaming_map,
    template_domaint &_template_domain,
    bv_pointerst &_solver, const namespacet &_ns) :
    renaming_map(_renaming_map),
    template_domain(_template_domain),
      solver(_solver), ns(_ns),activation_literal_counter(0)
  { 
    // adding program constraints to solver db
    for(constraintst::const_iterator it = program.begin(); it != program.end(); it++)
    {
      solver << *it;
    }
  }

  virtual void solve(invariantt &inv, const strategyt &strategy) { assert(false); }

  virtual bool improve(const invariantt &inv, strategyt &strategy);

 protected: 
  replace_mapt &renaming_map;
  
  inline void rename(exprt::operandst &operands)
  {
    for(unsigned i=0; i<operands.size(); ++i)
      replace_expr(renaming_map, operands[i]);
  }
  
  template_domaint &template_domain;
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

};

#endif
