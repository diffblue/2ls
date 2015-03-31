/*******************************************************************\

Module: Showing Stuff

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SUMMARIZER_SHOW_H
#define CPROVER_SUMMARIZER_SHOW_H

#include <string>
#include <ostream>

#include <goto-programs/goto_model.h>

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

#endif
