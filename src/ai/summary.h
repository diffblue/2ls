#ifndef CPROVER_DELTACHECK_SUMMARY_H
#define CPROVER_DELTACHECK_SUMMARY_H

#include <util/std_expr.h>
#include "predicate.h"

class summaryt
{
 public:
  typedef std::vector<symbol_exprt> var_listt;
  var_listt entry_vars, exit_vars;

  //void from_fixedpoint(class ssa_fixed_pointt &);
  
  // a summary has two parts:
  // 1) precondition (a predicate over entry_vars)
  // 2) transformer (a predicate over entry_vars and exit_vars)
  
  predicatet precondition;
  predicatet transformer;
};

#endif
