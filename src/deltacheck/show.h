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

void show_ssa(
  const indext &index,
  std::ostream &,
  message_handlert &);

void show_defs(
  const indext &index,
  std::ostream &,
  message_handlert &);

void show_fixed_points(
  const indext &index,
  std::ostream &,
  message_handlert &);

#endif
