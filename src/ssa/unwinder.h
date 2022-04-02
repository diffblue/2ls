/*******************************************************************\

Module: Unwinder

Author: František Nečas

\*******************************************************************/

/// \file
/// An interface of an SSA unwinder.

#ifndef CPROVER_2LS_SSA_UNWINDER_H
#define CPROVER_2LS_SSA_UNWINDER_H

#include "local_ssa.h"

/// Represents the mode which an unwinder operates in.
enum class unwinder_modet
{
  /// No specific behaviour requested, simply unwind.
  NORMAL,
  /// Bounded model checking is being performed. Add constraints
  /// only in the base case.
  BMC,
  /// K-induction is being performed, add constraints and also hoisted
  /// assertions.
  K_INDUCTION,
};

/// An abstract class representing an SSA unwinder of a single function.
class local_unwindert
{
public:
  /// Performs initializing actions that need to be done before the first
  /// unwinding.
  virtual void init()=0;

  /// Performs unwinding of all loops in the function up to bound k
  /// \param k The target unwind count which should be present after
  ///   unwinding the loop.
  /// \pre The unwinder has been initialized using \ref init
  virtual void unwind(unsigned k)=0;

  /// Gathers conditions under which loops continue.
  /// \param loop_cont Store for the gathered conditions.
  virtual void loop_continuation_conditions(
    exprt::operandst& loop_cont) const=0;

  /// Renames a variable based on the current unwinding.
  /// \param var Variable to rename.
  /// \param node SSA node providing context under which the rename
  ///   should occur.
  /// \param pre If set to false, 0-th unwind (base loop) will be considered.
  virtual void unwinder_rename(
    symbol_exprt &var,
    const local_SSAt::nodet &node,
    bool pre) const=0;

  /// The bound up to which loops are currently unwound.
  long current_unwinding=-1;
};

/// An abstract class representing an SSA unwinder of the whole program.
class unwindert
{
public:
  /// Creates local unwinders for each function operating in the given mode.
  /// \param mode Mode under which the unwinders should be initialized.
  virtual void init(unwinder_modet mode)=0;

  /// Runs initializing actions in all present local unwinders.
  virtual void init_localunwinders()=0;

  /// Unwinds all functions up to the given bound k.
  /// \param k The target unwind count which should be present after
  ///   unwinding the loop.
  virtual void unwind_all(unsigned k)=0;

  /// Returns a local unwinder for the given function name.
  /// \param fname Name of the function to get the unwinder of.
  virtual local_unwindert &get(const irep_idt &fname)=0;
  /// Returns a const local unwinder for the given function name.
  /// \param fname Name of the function to get the unwinder of.
  virtual const local_unwindert &get(const irep_idt &fname) const=0;
};

#endif
