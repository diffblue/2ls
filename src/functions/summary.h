/*******************************************************************\

Module: Function Summary

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef DELTACHECK_SUMMARY_H
#define DELTACHECK_SUMMARY_H

#include "../solver/predicate.h"

class summaryt
{
public:
  // signature
  predicatet::state_var_listt entry_vars, exit_vars;

  // build from fixedpoint
  void from_fixedpoint(class ssa_fixed_pointt &);
  
  // a summary has two parts:
  // 1) pre-state (a predicate over entry_vars)
  // 2) transformer (a predicate over entry_vars and exit_vars)
  
  predicatet pre_state;
  predicatet transformer;
};

#endif
