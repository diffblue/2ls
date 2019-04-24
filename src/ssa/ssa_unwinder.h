/*******************************************************************\

Module: SSA Unwinder

Author: Peter Schrammel, Saurabh Joshi

\*******************************************************************/

/// \file
/// SSA Unwinder

#ifndef CPROVER_2LS_SSA_SSA_UNWINDER_H
#define CPROVER_2LS_SSA_SSA_UNWINDER_H

#include "unwindable_local_ssa.h"
#include "ssa_db.h"

class ssa_local_unwindert
{
public:
  typedef local_SSAt::locationt locationt;
  typedef unwindable_local_SSAt::odometert odometert;

  ssa_local_unwindert(
    const irep_idt _fname,
    unwindable_local_SSAt& _SSA,
    bool _is_kinduction,
    bool _is_bmc):
    fname(_fname),
    SSA(_SSA),
    is_kinduction(_is_kinduction),
    is_bmc(_is_bmc)
  {
  }

  void init();

  void unwind(unsigned k);

#if 0
  // TODO: not yet sure how to do that
  void unwind(locationt loop_head_loc, unsigned k)
  {
    unwind(loops[loop_head_loc], k);
  }
#endif

  // TODO: this should be loop specific in future,
  // maybe move to unwindable_local_ssa as it is not really unwinder related
  void loop_continuation_conditions(exprt::operandst& loop_cont) const;

#if 0
  // TODO: these two should be possible with unwindable_local_ssa facilities
  exprt rename_invariant(const exprt& inv_in) const;
  void unwinder_rename(
    symbol_exprt &var,
    const local_SSAt::nodet &node,
    bool pre) const;
#endif

  // TODO: this must go away, should use SSA.rename instead
  void unwinder_rename(
    symbol_exprt &var,
    const local_SSAt::nodet &node,
    bool pre) const;

  class loopt // loop tree
  {
  public:
    loopt():
      is_dowhile(false),
      is_root(false),
      current_unwinding(-1)
    {
    }

    local_SSAt::nodest body_nodes;
    // pointer to loop end nodes in SSA for updating current loop head
    std::map<odometert, local_SSAt::nodest::iterator> end_nodes;
    std::vector<unsigned> loop_nodes; // child loops
    bool is_dowhile;
    bool is_root;
    long current_unwinding;
    typedef std::map<exprt, exprt::operandst> exit_mapt;
    exit_mapt exit_map;
    std::map<symbol_exprt, symbol_exprt> pre_post_map;
    std::vector<exprt> modified_vars;

    // for assertion hoisting
    typedef struct
    {
      exprt::operandst exit_conditions;
      exprt::operandst assertions;
    } assertions_after_loopt;
    typedef std::map<locationt, assertions_after_loopt> assertion_hoisting_mapt;
    assertion_hoisting_mapt assertion_hoisting_map;
  };

  bool find_loop(unsigned location_number, const loopt *&loop) const;

protected:
  const irep_idt fname;
  unwindable_local_SSAt &SSA;
  bool is_kinduction, is_bmc;
  symbol_exprt current_enabling_expr; // TODO must become loop-specific

  // use location numbers as indices, as target addresses make
  //  things non-deterministic
  typedef std::map<unsigned, loopt> loop_mapt;
  loop_mapt loops;

  void build_loop_tree();
  void build_pre_post_map();
  void build_exit_conditions();

  void unwind(loopt &loop, unsigned k, bool is_new_parent);

  exprt get_continuation_condition(const loopt& loop) const;
  void loop_continuation_conditions(
    const loopt& loop,
    exprt::operandst &loop_cont) const;

  void add_loop_body(loopt &loop);
  void add_assertions(loopt &loop, bool is_last);
  void add_loop_head(loopt &loop);
  void add_loop_connector(loopt &loop);
  void add_exit_merges(loopt &loop, unsigned k);
  equal_exprt build_exit_merge(
    exprt e,
    const exprt &exits,
    unsigned k,
    locationt loc);
  void add_hoisted_assertions(loopt &loop, bool is_last);
};

class ssa_unwindert:public messaget
{
public:
  typedef std::map<irep_idt, ssa_local_unwindert> unwinder_mapt;
  typedef std::pair<irep_idt, ssa_local_unwindert> unwinder_pairt;

  explicit ssa_unwindert(ssa_dbt& _db):
    ssa_db(_db),
    is_initialized(false)
  {
  }

  void init(bool is_kinduction, bool is_bmc);
  void init_localunwinders();

  void unwind(const irep_idt fname, unsigned k);
  void unwind_all(unsigned k);

  inline ssa_local_unwindert &get(const irep_idt& fname)
  {
    return unwinder_map.at(fname);
  }

  inline const ssa_local_unwindert &get(const irep_idt& fname) const
  {
    return unwinder_map.at(fname);
  }

protected:
  ssa_dbt &ssa_db;
  bool is_initialized;
  unwinder_mapt unwinder_map;
};

#endif
