#include "inv.h"

class strategy_solver_baset 
{
 public:
  typedef template_domaint::invariantt invariantt;
  typedef std::mapt<template_domaint::rowt, multiplexer_statet> strategyt;

  strategy_solvert(const local_SSAt &program, loopvarst loopvars, 
    template_domaint &template_domain) {}

  virtual void solve(invariantt &inv, const strategyt &strategy) { assert(false); }

  virtual bool improve(const invariantt &inv, strategyt &strategy);

 protected:
  solvert solver;
};
