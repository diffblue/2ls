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
    goto_modelt &_goto_model,
    const irep_idt &_function_name,
    goto_functiont &_goto_function,
    unwinder_modet _mode,
    bool _simplify):
    ssa_db(_ssa_db),
    goto_model(_goto_model),
    function_name(_function_name),
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
  /// A flag which is used for marking unwind starts inside the GOTO program.
  const irep_idt unwind_flag="unwind";
  /// Reference to a global storage of SSA.
  ssa_dbt &ssa_db;
  /// The whole GOTO model. Required for calling update() and accessing the
  /// symbol table for SSA recomputing.
  goto_modelt &goto_model;
  /// Name of the function to unwind.
  const irep_idt &function_name;
  /// The GOTO function which this unwinder unwinds.
  goto_functiont &goto_function;
  /// Mode under which the unwinder operates.
  unwinder_modet mode;
  /// Whether the unwound SSA should be simplified.
  bool simplify;
  /// A store used for keeping track of how loops were formerly connected
  /// before transformations required for k-induction or BMC to correctly
  /// work were done.
  std::unordered_map<unsigned, goto_programt::targett> loop_targets;

  void unwind_function(unsigned to_unwind);
  void mark_unwinds(
    const goto_programt::targett before_unwind,
    const std::vector<goto_programt::targett> &iteration_points,
    unsigned to_unwind);
  void reconnect_loops();
  void reset_loop_connections();
  void recompute_ssa();
  void update_ssa(
    local_SSAt &SSA,
    const goto_programt &goto_program);
  void update_assertions(
    local_SSAt &SSA,
    const goto_programt &goto_program);
  void add_hoisted_assertions(
    local_SSAt &SSA,
    const goto_programt &goto_program);
  void convert_to_constraints(
    local_SSAt &SSA,
    local_SSAt::nodest::iterator &ssa_it,
    local_SSAt::nodest::iterator &loop_back,
    bool is_last);
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
