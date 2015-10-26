/*******************************************************************\

Module: SSA Unwinder Infrastructure

Author: Peter Schrammel, Saurabh Joshi

\*******************************************************************/

#ifndef CPROVER_DELTACHECK_SSA_UNWINDABLE_LOCAL_SSA_H
#define CPROVER_DELTACHECK_SSA_UNWINDABLE_LOCAL_SSA_H

#include <util/message.h>

#include "local_ssa.h"

class unwindable_local_SSAt : public local_SSAt
{
public:
  unwindable_local_SSAt(
    const goto_functiont &_goto_function,
    const namespacet &_ns,
    const std::string &_suffix="")
    :
    local_SSAt(_goto_function,_ns,_suffix),
    current_unwinding(-1)
  {
    compute_loop_hierarchy();
  }

  virtual ~unwindable_local_SSAt() {}

  virtual symbol_exprt name(const ssa_objectt &, 
			    kindt kind, locationt loc) const;
  virtual exprt nondet_symbol(std::string prefix, const typet &type, 
			      locationt loc, unsigned counter) const;

  typedef std::vector<unsigned> odometert;
  odometert current_unwindings;
  long current_unwinding; //TODO: must go away

  // mode==0: current, mode>0 push, mode<0 pop
  void increment_unwindings(int mode);
  // mode==0: current, mode>0 push, mode<0 pop
  void decrement_unwindings(int mode);
  std::string odometer_to_string(const odometert &odometer, 
				 unsigned level) const;

  void rename(exprt &expr);

  typedef std::map<local_SSAt::locationt,unsigned>
    loop_hierarchy_levelt;
  loop_hierarchy_levelt loop_hierarchy_level;

protected:
  irep_idt get_ssa_name(const symbol_exprt &, locationt &loc);
  void compute_loop_hierarchy();

};

#endif
