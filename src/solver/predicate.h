/*******************************************************************\

Module: Delta Checking Abstract State

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_DELTACHECK_PREDICATE_H
#define CPROVER_DELTACHECK_PREDICATE_H

#include <util/std_expr.h>
#include <util/union_find.h>
#include <util/threeval.h>

#include "solver.h"

struct predicatet
{
public:
  predicatet()
  {
  }

  // support set of the predicate
  typedef std::vector<symbol_exprt> state_var_listt;
  state_var_listt state_vars;

  void output(std::ostream &) const;
  void make_false();
  
  // returns 'true' iff predicate is weakened
  bool disjunction(const predicatet &);
  
  // rename supporting set of variables
  void rename(const state_var_listt &new_state_vars);
    
  // read the predicate from a solver state  
  void get(const solvert &);
  
  // push the predicate to a solver as constraint
  void set_to_true(decision_proceduret &) const;

  bool is_bottom() const
  {
    return false;
  }

  bool is_top() const
  {
    for(unsigned i=0; i<uuf.size(); i++)
      if(uuf.find(i)!=i)
        return false;

    return true;
  }

protected:
  // for now, we can track:
  // * equalities between variables
  // * intervals

  unsigned_union_find uuf;

  typedef expanding_vector<integer_intervalt> integer_intervalst;
  typedef expanding_vector<ieee_float_intervalt> ieee_float_intervalst;
  integer_intervalst integer_intervals;
  ieee_float_intervalst ieee_float_intervals;
};

static inline std::ostream & operator << (
  std::ostream &out, const predicatet &predicate)
{
  predicate.output(out);
  return out;
}

static inline decision_proceduret & operator << (
  decision_proceduret &dest, const predicatet &predicate)
{
  predicate.set_to_true(dest);
  return dest;
}

#endif
