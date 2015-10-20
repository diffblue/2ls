/*******************************************************************\

Module: SSA Unwinder

Author: Saurabh Joshi, Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_DELTACHECK_SSA_UNWINDER2_H
#define CPROVER_DELTACHECK_SSA_UNWINDER2_H

#include "unwindable_local_ssa.h"

class ssa_local_unwinder2t
{
public:
  typedef local_SSAt::locationt locationt;
  typedef unwindable_local_SSAt::odometert odometert;
  
  ssa_local_unwinder2t(local_SSAt& _SSA, bool _is_kinduction, bool _is_ibmc)
    :
  SSA(_SSA), is_kinduction(_is_kinduction), is_ibmc(_is_ibmc)
  {}

  void init();

  void unwind(unsigned k);

  //TODO: not yet sure how to do that
/*  void unwind(locationt loop_head_loc, unsigned k)
    { unwind(loops[loop_head_loc],k); } */

  //TOOD: this should be loop specific in future, maybe move to unwindable_local_ssa as it is not really unwinder related
  void loop_continuation_conditions(exprt::operandst& loop_cont_e) const;

  //TODO: these two should be possible with unwindable_local_ssa facilities
  //exprt rename_invariant(const exprt& inv_in) const; 
  //void unwinder_rename(symbol_exprt &var,const local_SSAt::nodet &node, bool pre) const;

protected:
  local_SSAt& SSA;
  bool is_kinduction,is_ibmc;

  class loopt //loop tree
  {
  public:
    loopt()
      :
    is_dowhile(false),
    is_root(false),
    current_unwinding(0)
    {}

    local_SSAt::nodest body_nodes;
    std::vector<locationt> loop_nodes; //child loops
    exprt loop_continuation_condition;
    bool is_dowhile;
    bool is_root;
    unsigned current_unwinding;
    exprt::operandst loop_exit_conditions;

    //for assertion hoisting
    struct {
      exprt loop_exit_condition;
      exprt assertion;
    } assertions_after_loopt;
    typedef std::map<locationt,assertions_after_loopt> assertion_hoisting_mapt;
    assertion_hoisting_mapt assertion_hoisting_mapt;

  };
  typedef std::map<locationt,loopt> loop_mapt;
  loop_mapt loops;

  void unwind(loopt &loop, unsigned k);

  void add_loop_body(loopt &loop,  const odometert &unwindings);
  void add_loop_connectors(loopt &loop,  const odometert &unwindings);
  void add_exit_merges(loopt &loop,  const odometert &unwindings);
  void add_assertions(loopt &loop,  const odometert &unwindings);
  void add_hoisted_assertions(loopt &loop,  const odometert &unwindings);
  
};

#endif
