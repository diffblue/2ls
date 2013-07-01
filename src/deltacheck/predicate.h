/*******************************************************************\

Module: Delta Checking Solver

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_DELTACHECK_PREDICATE_H
#define CPROVER_DELTACHECK_PREDICATE_H

#include <util/std_expr.h>

#include "solver.h"

struct predicatet
{
public:
  typedef std::vector<symbol_exprt> var_listt;

  symbol_exprt guard;
  var_listt vars;

  void output(std::ostream &) const;

  void make_false()
  {
    is_false=true;
  }
  
  // returns 'true' iff predicate is weakened
  bool disjunction(const predicatet &);
  
  // rename supporting set of variables
  void rename(
    const symbol_exprt &new_guard,
    const var_listt &new_vars);
    
  predicatet():is_false(false)
  {
  }
  
  void get(const solvert &);
  void set_to_true(solvert &) const;

protected:
  bool is_false;
};

static inline std::ostream & operator << (
  std::ostream &out, const predicatet &predicate)
{
  predicate.output(out);
  return out;
}

#endif
