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
  bool simplify,
  std::ostream &,
  message_handlert &);

void show_defs(
  const goto_modelt &,
  std::ostream &,
  message_handlert &);

void show_guards(
  const goto_modelt &,
  std::ostream &,
  message_handlert &);

/*
void show_fixed_points(
  const goto_modelt &,
  std::ostream &,
  message_handlert &);
*/

#endif
