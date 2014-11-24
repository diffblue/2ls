/*******************************************************************\

Module: Summary

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_DELTACHECK_SUMMARY_H
#define CPROVER_DELTACHECK_SUMMARY_H

#include <iostream>
#include <set>

#include <util/std_expr.h>

class summaryt
{
 public:
  typedef exprt predicatet;

  typedef std::list<symbol_exprt> var_listt;
  typedef std::set<symbol_exprt> var_sett;
  var_listt params;
  var_sett globals_in, globals_out;

  explicit summaryt() : mark_recompute(false) {};

  //void from_fixedpoint(class ssa_fixed_pointt &);
  
  // a summary has two parts:
  // 1) precondition (a predicate over entry_vars (and exit_vars))
  // 2) transformer (a predicate over entry_vars and exit_vars)
  
  predicatet precondition; //let's call it the caller-based summary
  predicatet transformer; // this is the callee-based summary
  predicatet invariant; 

  bool mark_recompute; //to force recomputation of the summary
                       // (used for invariant reuse in k-induction)

  void output(std::ostream &out, const namespacet &ns) const;

  void join(const summaryt &new_summary);

 protected:

  void combine_or(exprt &olde, const exprt &newe);
  void combine_and(exprt &olde, const exprt &newe);

};


#endif
