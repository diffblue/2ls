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
    var_listt &_pre_state_vars, var_listt &_post_state_vars,
    template_domaint &_template_domain,
    bv_pointerst &_solver, const namespacet &_ns) :
    pre_state_vars(_pre_state_vars), post_state_vars(_post_state_vars),
    template_domain(_template_domain),
      solver(_solver), ns(_ns),activation_literal_counter(0)
  {
    // build replace map
    assert(pre_state_vars.size()==post_state_vars.size());
    var_listt::const_iterator it1=pre_state_vars.begin();
    var_listt::const_iterator it2=post_state_vars.begin();
  
    for(; it1!=pre_state_vars.end(); ++it1, ++it2)
    {
      renaming_map[*it1]=*it2;    
    }
  
    // adding program constraints to solver db
    for(constraintst::const_iterator it = program.begin(); it != program.end(); it++)
    {
      solver << *it;
    }
  }

  virtual void solve(invariantt &inv, const strategyt &strategy) { assert(false); }

  virtual bool improve(const invariantt &inv, strategyt &strategy);

 protected:
  var_listt &pre_state_vars;
  var_listt &post_state_vars;
  
  replace_mapt renaming_map;
  
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
