/*******************************************************************\

Module: Predicates

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_DELTACHECK_PREDICATES_H
#define CPROVER_DELTACHECK_PREDICATES_H

#include <expr.h>

#include <cuddObj.hh>

struct predicatet
{
  irep_idt id;
  exprt expr;
  
  // the BDD variable for the predicate and the next-state version
  BDD var, next_var;
};
  
typedef std::vector<predicatet> predicatest;

#endif
