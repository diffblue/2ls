/*******************************************************************\

Module: Unwinder

Author: František Nečas

\*******************************************************************/

/// \file
/// An interface of an SSA unwinder.

#ifndef CPROVER_2LS_SSA_UNWINDER_H
#define CPROVER_2LS_SSA_UNWINDER_H

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

#endif
