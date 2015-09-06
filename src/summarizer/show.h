/*******************************************************************\

Module: Showing Stuff

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SUMMARIZER_SHOW_H
#define CPROVER_SUMMARIZER_SHOW_H

#include <string>
#include <ostream>

#include <solvers/prop/prop_conv.h>

#include <goto-programs/goto_model.h>

#include "summary.h"

class message_handlert;

void show_ssa(
  const goto_modelt &,
  const irep_idt &function,
  bool simplify,
  std::ostream &,
  message_handlert &);

void show_defs(
  const goto_modelt &,
  const irep_idt &function,
  std::ostream &,
  message_handlert &);

void show_value_sets(
  const goto_modelt &,
  const irep_idt &function,
  std::ostream &,
  message_handlert &);

void show_assignments(
  const goto_modelt &,
  const irep_idt &function,
  std::ostream &,
  message_handlert &);

void show_guards(
  const goto_modelt &,
  const irep_idt &function,
  std::ostream &,
  message_handlert &);

void show_fixed_points(
  const goto_modelt &,
  const irep_idt &function,
  bool simplify,
  std::ostream &,
  message_handlert &);

//shows raw error trace
void show_error_trace(
  const irep_idt &property_id,
  const local_SSAt &SSA, 
  prop_convt &solver,
  std::ostream &,
  message_handlert &);

void show_invariants(
  const local_SSAt &SSA, 
  const summaryt &summary,
  std::ostream &out);

void show_ssa_symbols(
  const local_SSAt &SSA, 
  std::ostream &out);

#endif
