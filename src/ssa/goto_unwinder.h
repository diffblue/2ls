/*******************************************************************\
Module: SSA Unwinder
Author: František Nečas
\*******************************************************************/

/// \file
/// SSA Unwinder that unwinds the SSA by unwinding the given GOTO
/// program and converting the unwound program back to SSA rather
/// than unwinding on the SSA level. This enables 2LS to unwind
/// loops which create dynamic objects (points-to analysis
/// is kept in sync with the actual state of dynamic objects).
///
/// The current implementation doesn't utilise incremental SAT solving
/// correctly so its performance is hindered, however it produces more
/// sound results in the case of programs with dynamic memory.
/// Moreover due to the current implementation of summary_checker_nonterm,
/// (relying on renames based on % suffixes), nontermination support
/// is not possible in this type of implementation.

#ifndef CPROVER_2LS_SSA_GOTO_UNWINDER_H
#define CPROVER_2LS_SSA_GOTO_UNWINDER_H

#include "unwindable_local_ssa.h"
#include "unwinder.h"
#include "ssa_db.h"

class goto_local_unwindert:public local_unwindert, messaget
{
public:
  goto_local_unwindert(
    ssa_dbt &_ssa_db,
    goto_functiont &_goto_function,
    unwinder_modet _mode,
    bool _simplify):
    ssa_db(_ssa_db),
    goto_function(_goto_function),
    mode(_mode),
    simplify(_simplify)
  {
  }

  void init() override;
  void unwind(unsigned k) override;

  void loop_continuation_conditions(exprt::operandst& loop_cont) const override;
  void unwinder_rename(
    symbol_exprt &var,
    const local_SSAt::nodet &node,
    bool pre) const override;

protected:
  /// Reference to a global storage of SSA.
  ssa_dbt &ssa_db;
  /// The GOTO function which this unwinder unwinds.
  goto_functiont &goto_function;
  /// Mode under which the unwinder operates.
  unwinder_modet mode;
  /// Whether the unwound SSA should be simplified.
  bool simplify;
};


/// An SSA unwinder that unwinds the given GOTO and then transforms
/// the changes into SSA.
class goto_unwindert:public unwindert, messaget
{
public:
  explicit goto_unwindert(
    ssa_dbt &_ssa_db,
    goto_modelt &_goto_model,
    bool _simplify) :
    ssa_db(_ssa_db),
    goto_model(_goto_model),
    simplify(_simplify),
    is_initialized(false)
  {}

  void init(unwinder_modet mode) override;
  void init_localunwinders() override;

  void unwind_all(unsigned k) override;

  inline goto_local_unwindert &get(const irep_idt& fname) override
  {
    return unwinder_map.at(fname);
  }

  inline const goto_local_unwindert &get(const irep_idt& fname) const override
  {
    return unwinder_map.at(fname);
  }

protected:
  typedef std::map<irep_idt, goto_local_unwindert> unwinder_mapt;

  /// Reference to a global storage of SSA.
  ssa_dbt &ssa_db;
  /// Reference to a GOTO program tied to this unwinder.
  goto_modelt &goto_model;
  /// Whether the unwound SSA should be simplified.
  bool simplify;
  /// Whether the unwinder is fully initialized.
  bool is_initialized;
  /// Maps function names to their respective local unwinders.
  unwinder_mapt unwinder_map;
};

#endif
