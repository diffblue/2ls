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
  
  predicatet::state_var_listt pre_state_vars, post_state_vars;
  
  predicatet state_predicate;

  void output(std::ostream &) const;
  
  unsigned iteration_number;

  void operator()();

protected:
  const namespacet &ns;

  // fixed-point iteration
  void initialize();
  bool iteration();
};

static inline decision_proceduret & operator << (
  decision_proceduret &dest,
  const std::list<exprt> &src)
{
  for(std::list<exprt>::const_iterator
      c_it=src.begin(); c_it!=src.end(); c_it++)
    dest << *c_it;
  return dest;
}

#endif
