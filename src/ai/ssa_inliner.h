#ifndef CPROVER_DELTACHECK_SSA_INLINER_H
#define CPROVER_DELTACHECK_SSA_INLINER_H

#include "summary.h"
#include "../ssa/local_ssa.h"

class ssa_inlinert
{
 public:
  ssa_inlinert() : counter(0) {}

  //assumption: the node containing the function call has a single equality

  void replace(local_SSAt::nodet &node, 
                       local_SSAt::nodet::equalitiest::iterator equ_it, 
                       summaryt summary);

  void replace(local_SSAt::nodet &node, 
                       local_SSAt::nodet::equalitiest::iterator equ_it, 
                       const local_SSAt &function);

  void havoc(local_SSAt::nodet &node, 
	     local_SSAt::nodet::equalitiest::iterator &equ_it);

 protected:
  unsigned counter;

  void rename(exprt &expr);

};


#endif
