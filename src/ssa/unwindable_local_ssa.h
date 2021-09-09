/*******************************************************************\

Module: SSA Unwinder Infrastructure

Author: Peter Schrammel, Saurabh Joshi

\*******************************************************************/

/// \file
/// SSA Unwinder Infrastructure

#ifndef CPROVER_2LS_SSA_UNWINDABLE_LOCAL_SSA_H
#define CPROVER_2LS_SSA_UNWINDABLE_LOCAL_SSA_H

#include <util/message.h>

#include "local_ssa.h"

class unwindable_local_SSAt:public local_SSAt
{
public:
  unwindable_local_SSAt(
    const irep_idt &function_identifier,
    const goto_functiont &_goto_function,
    const symbol_tablet &_symbol_table,
    const optionst &_options,
    const std::string &_suffix=""):
    local_SSAt(
      function_identifier,
      _goto_function,
      _symbol_table,
      _options,
      _suffix),
    current_unwinding(-1)
  {
    compute_loop_hierarchy();
  }

  virtual ~unwindable_local_SSAt() {}

  virtual symbol_exprt name(
    const ssa_objectt &obj,
    kindt kind,
    locationt loc) const override
  {
    return name(obj, kind, loc, loc);
  }
  symbol_exprt name(
    const ssa_objectt &,
    kindt,
    locationt def_loc,
    locationt current_loc) const;
  virtual exprt nondet_symbol(
    std::string prefix,
    const typet &type,
    locationt loc,
    unsigned counter) const override;

  // control renaming during unwindings
  typedef std::vector<unsigned> odometert;
  odometert current_unwindings;
  long current_unwinding; // TODO: must go away
  locationt current_location; // TOOD: must go away, not sure how;

  // mode==0: current, mode>0 push, mode<0 pop
  void increment_unwindings(int mode);
  // mode==0: current, mode>0 push, mode<0 pop
  void decrement_unwindings(int mode);
  std::string odometer_to_string(
    const odometert &odometer,
    unsigned level) const;

  void rename(exprt &expr, locationt loc);

  typedef struct
  {
    unsigned level;
    unsigned loop_number;
    local_SSAt::locationt parent_loc;
  }
  loop_hierarchy_infot;

  typedef std::map<local_SSAt::locationt, loop_hierarchy_infot>
    loop_hierarchy_levelt;
  loop_hierarchy_levelt loop_hierarchy_level;

  irep_idt get_full_ssa_name(
    const symbol_exprt &symbol_expr,
    locationt &loc,
    odometert &odometer) const;

  void output_verbose(std::ostream &) const override;

protected:
  irep_idt get_ssa_name(const symbol_exprt &, locationt &loc) const;

  unsigned get_def_level(locationt def_loc, locationt current_loc) const;
  void compute_loop_hierarchy();
};

#endif
