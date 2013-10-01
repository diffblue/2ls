/*******************************************************************\

Module: Forward Greatest Fixed-Point

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef DELTACHECK_FIXED_POINT_H
#define DELTACHECK_FIXED_POINT_H

#include "solver.h"
#include "predicate.h"

class fixed_pointt
{
public:
  explicit fixed_pointt(const namespacet &_ns):ns(_ns)
  {
  }  

  typedef std::list<exprt> constraintst;
  constraintst transition_relation;
  
  typedef std::vector<symbol_exprt> var_listt;  
  var_listt pre_state_vars, post_state_vars;
  var_listt pre_state_guards, post_state_guards;
  
  predicatet state_predicate;

  void print(std::ostream &) const;
  
  unsigned iteration_number;

  void fixed_point();

protected:
  const namespacet &ns;

  // fixed-point iteration
  void initialize();
  bool iteration();
};

#endif
