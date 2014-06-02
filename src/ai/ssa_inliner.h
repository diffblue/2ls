/*******************************************************************\

Module: SSA Inliner

Author: Peter Schrammel

\*******************************************************************/

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

  //TODO: problem: local_SSAt::nodest maps a goto program target to a single SSA node,
  //               for inlining we require a target to map to several SSA nodes
  void replace(local_SSAt::nodest &nodes,
		       local_SSAt::nodet &node, 
                       local_SSAt::nodet::equalitiest::iterator equ_it, 
                       const local_SSAt &function);

  void havoc(local_SSAt::nodet &node, 
	     local_SSAt::nodet::equalitiest::iterator &equ_it);

 protected:
  unsigned counter;

  void rename(exprt &expr);

};


#endif
