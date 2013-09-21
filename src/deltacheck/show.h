/*******************************************************************\

Module: SSA Showing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SHOW_H
#define CPROVER_SHOW_H

#include <string>
#include <ostream>

class message_handlert;
class indext;
class optionst;

void show_ssa(
  const indext &index,
  const optionst &options,
  std::ostream &,
  message_handlert &);

void show_defs(
  const indext &index,
  const optionst &options,
  std::ostream &,
  message_handlert &);

void show_guards(
  const indext &index,
  const optionst &options,
  std::ostream &,
  message_handlert &);

void show_fixed_points(
  const indext &index,
  const optionst &options,
  std::ostream &,
  message_handlert &);

void show_properties(
  const indext &index,
  const optionst &options,
  std::ostream &,
  message_handlert &);

#endif
