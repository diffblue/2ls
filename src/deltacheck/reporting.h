/*******************************************************************\

Module: Collation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_DELTACHECK_REPORTING_H
#define CPROVER_DELTACHECK_REPORTING_H

#include <vector>
#include <string>

#include <util/options.h>
#include <util/message.h>

void reporting_html(
  const std::list<std::string> &files,
  const optionst &,
  message_handlert &);

void reporting_cmdline(
  const std::list<std::string> &files,
  const optionst &,
  message_handlert &);

#endif
