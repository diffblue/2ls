/*******************************************************************\

Module: SSA Unwinder Infrastructure

Author: Peter Schrammel, Saurabh Joshi

\*******************************************************************/

#ifndef CPROVER_DELTACHECK_SSA_UNWINDER2_H
#define CPROVER_DELTACHECK_SSA_UNWINDER2_H

#include <util/message.h>

#include "../ssa/local_ssa.h"

class ssa_local_unwinder2t
{
public:
  ssa_local_unwinder2t(
    const local_SSAt &_SSA)
    :
  SSA(_SSA)
  {
    compute_loop_hierarchy();
  }

  typedef std::vector<unsigned> odometert;

//  unsigned current_unwinding; //TODO: loop-specific unwindings in future

  // mode==0: current, mode>0 push, mode<0 pop
  void increment_unwindings(odometert &unwindings, 
			    int mode);
  // mode==0: current, mode>0 push, mode<0 pop
  void decrement_unwindings(odometert &unwindings, 
			    int mode);
  std::string odometer_to_string(const odometert &odometer, 
				 unsigned level);

  void rename(symbol_exprt &expr, 
	      const odometert &unwindings);
  void read_rhs(exprt &expr, 
		const odometert &unwindings,
		local_SSAt::locationt loc);

  typedef std::map<local_SSAt::locationt,unsigned>
    loop_hierarchy_levelt;
  loop_hierarchy_levelt loop_hierarchy_level;

protected:
  const local_SSAt &SSA;

  void compute_loop_hierarchy();

};

#endif
