#ifndef CPROVER_STRATEGY_SOLVER_BASE
#define CPROVER_STRATEGY_SOLVER_BASE 

#include <map>
#include "template_domain.h"

class strategy_solver_baset 
{
 public:
  typedef std::list<exprt> constraintst;
  typedef predicatet::state_var_listt var_listt;
  typedef template_domaint::valuet invariantt;
  typedef std::vector<template_domaint::rowt> strategyt;

  strategy_solver_baset(const constraintst &program,
    const var_listt &_pre_state_vars, const var_listt &_post_state_vars,
    template_domaint &_template_domain,
    prop_convt &_solver) :
    pre_state_vars(_pre_state_vars), post_state_vars(_post_state_vars),
    template_domain(_template_domain),
    solver(_solver)
  {
    solver << program;
  }

  virtual void solve(invariantt &inv, const strategyt &strategy) { assert(false); }

  virtual bool improve(const invariantt &inv, strategyt &strategy);

 protected:
  var_listt &pre_state_vars;
  var_listt &post_state_vars;
  template_domaint &template_domain;
  prop_convt &solver;

};

#endif
