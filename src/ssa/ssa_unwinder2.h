/*******************************************************************\

Module: SSA Unwinder

Author: Peter Schrammel, Saurabh Joshi

\*******************************************************************/

#ifndef CPROVER_DELTACHECK_SSA_UNWINDER2_H
#define CPROVER_DELTACHECK_SSA_UNWINDER2_H

#include "unwindable_local_ssa.h"

class ssa_local_unwinder2t
{
public:
  typedef local_SSAt::locationt locationt;
  typedef unwindable_local_SSAt::odometert odometert;
  
  ssa_local_unwinder2t(const irep_idt& _fname, unwindable_local_SSAt& _SSA,
		       bool _is_kinduction, bool _is_ibmc)
    :
    fname(_fname),SSA(_SSA), is_kinduction(_is_kinduction), is_ibmc(_is_ibmc),
    current_enabling_expr(true_exprt())
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
  const irep_idt& fname;
  unwindable_local_SSAt& SSA;
  bool is_kinduction,is_ibmc;
  exprt current_enabling_expr; //TODO must become loop-specific

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
    exprt continuation_condition;
    bool is_dowhile;
    bool is_root;
    unsigned current_unwinding;
    exprt::operandst exit_conditions;
    std::map<symbol_exprt,symbol_exprt> pre_post_map;

    //for assertion hoisting
    typedef struct {
      exprt loop_exit_condition;
      exprt assertion;
    } assertions_after_loopt;
    typedef std::map<locationt,assertions_after_loopt> assertion_hoisting_mapt;
    assertion_hoisting_mapt assertion_hoisting_map;

  };
  typedef std::map<locationt,loopt> loop_mapt;
  loop_mapt loops;

  void build_loop_tree();
  void build_pre_post_map();
  void build_continuation_conditions();
  void build_exit_conditions();

  void unwind(loopt &loop, unsigned k);
  
  void add_loop_body(loopt &loop);
  void add_loop_head(loopt &loop);
  void add_loop_connector(loopt &loop);
  void add_exit_merges(loopt &loop, unsigned k);
  void add_assertions(loopt &loop, unsigned k);
  void add_hoisted_assertions(loopt &loop, unsigned k);
  
};

#endif
