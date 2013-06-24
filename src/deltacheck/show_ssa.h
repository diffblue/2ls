/*******************************************************************\

Module: SSA Showing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SHOW_SSA_H
#define CPROVER_SHOW_SSA_H

#include <string>
#include <ostream>

class message_handlert;
class indext;

void show_ssa(
  const indext &index,
  std::ostream &,
  message_handlert &);

#endif
