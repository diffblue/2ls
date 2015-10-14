/*******************************************************************\

Module: SSA Unwinder Infrastructure

Author: Peter Schrammel, Saurabh Joshi

\*******************************************************************/

#ifndef CPROVER_DELTACHECK_SSA_UNWINDER2_H
#define CPROVER_DELTACHECK_SSA_UNWINDER2_H

#include <util/message.h>

#include "../ssa/local_ssa.h"

class ssa_local_unwinder2t : public local_SSAt
{
public:
  ssa_local_unwinder2t(
    const goto_functiont &_goto_function,
    const namespacet &_ns,
    const std::string &_suffix="")
    :
  local_SSAt(_goto_function,_ns,_suffix)
  {
    compute_loop_hierarchy();
  }

  virtual ~ssa_local_unwinder2t() {}

  virtual symbol_exprt name(const ssa_objectt &, kindt kind, locationt loc) const;

  typedef std::vector<unsigned> odometert;
  odometert current_unwindings;

//  unsigned current_unwinding; //TODO: loop-specific unwindings in future

  // mode==0: current, mode>0 push, mode<0 pop
  void increment_unwindings(int mode);
  // mode==0: current, mode>0 push, mode<0 pop
  void decrement_unwindings(int mode);
  std::string odometer_to_string(const odometert &odometer, 
				 unsigned level) const;

/*  void rename(symbol_exprt &expr, 
	      const odometert &unwindings);
  void read_rhs(exprt &expr, 
		const odometert &unwindings,
		local_SSAt::locationt loc);*/

  typedef std::map<local_SSAt::locationt,unsigned>
    loop_hierarchy_levelt;
  loop_hierarchy_levelt loop_hierarchy_level;

protected:
  void compute_loop_hierarchy();

};

#endif
