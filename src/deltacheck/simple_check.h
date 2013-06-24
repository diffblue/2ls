/*******************************************************************\

Module: Delta Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SIMPLE_CHECK_H
#define CPROVER_SIMPLE_CHECK_H

#include <string>

class message_handlert;
class indext;

void simple_check(
  const indext &index,
  const std::string &function,
  message_handlert &);

#endif
