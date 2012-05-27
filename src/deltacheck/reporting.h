/*******************************************************************\

Module: Collation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_DELTACHECK_REPORTING_H
#define CPROVER_DELTACHECK_REPORTING_H

#include <vector>
#include <string>

#include <options.h>
#include <message.h>

void reporting(
  const std::vector<std::string> &files,
  const optionst &,
  message_handlert &);

#endif
