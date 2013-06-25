/*******************************************************************\

Module: Def Domain Showing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SHOW_DEFS_H
#define CPROVER_SHOW_DEFS_H

#include <string>
#include <ostream>

class message_handlert;
class indext;

void show_defs(
  const indext &index,
  std::ostream &,
  message_handlert &);

#endif
