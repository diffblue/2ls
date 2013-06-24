/*******************************************************************\

Module: Delta Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_DELTA_CHECK_H
#define CPROVER_DELTA_CHECK_H

#include <string>

class message_handlert;
class indext;

void delta_check(
  const indext &index1,
  const indext &index2,
  const std::string &function,
  message_handlert &);

#endif
