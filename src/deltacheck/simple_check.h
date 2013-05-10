/*******************************************************************\

Module: Delta Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SIMPLE_CHECK_H
#define CPROVER_SIMPLE_CHECK_H

#include <string>

#include <util/message.h>

void simple_check(
  const std::string &index1,
  const std::string &function,
  message_handlert &);

#endif
