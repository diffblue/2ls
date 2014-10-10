/*******************************************************************\

Module: Summary

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_DELTACHECK_SUMMARY_H
#define CPROVER_DELTACHECK_SUMMARY_H

#include <iostream>
#include <set>

#include <util/std_expr.h>

typedef enum{YES, NO, UNKNOWN} threevalt;

class summaryt
{
 public:
  typedef exprt predicatet;

  typedef std::list<symbol_exprt> var_listt;
  typedef std::set<symbol_exprt> var_sett;

  summaryt() : 
    precondition(nil_exprt()), 
    transformer(true_exprt()), 
    invariant(true_exprt()), 
    termination_argument(nil_exprt()), 
    terminates(UNKNOWN) {}

  var_listt params;
  var_sett globals_in, globals_out;

  //void from_fixedpoint(class ssa_fixed_pointt &);
  
  // a summary has two parts:
  // 1) precondition (a predicate over entry_vars (and exit_vars))
  // 2) transformer (a predicate over entry_vars and exit_vars)
  
  predicatet precondition; //let's call it the caller-based summary
  predicatet transformer; // this is the callee-based summary
  predicatet invariant; 

  predicatet termination_argument;
  threevalt terminates;

  void output(std::ostream &out, const namespacet &ns) const;

};

std::string threeval2string(threevalt v);


#endif
