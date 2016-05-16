/*******************************************************************\

Module: Source Code Reporting

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_REPORT_SOURCE_CODE_H
#define CPROVER_REPORT_SOURCE_CODE_H

#include <ostream>

#include <util/message.h>
#include <goto-programs/goto_functions.h>

#include "properties.h"

void report_source_code(
  const std::string &path_prefix,
  const source_locationt &location,
  const goto_programt &goto_program,
  const propertiest &properties,
  std::ostream &,
  message_handlert &);

void report_source_code(
  const std::string &path_prefix_old,
  const source_locationt &location_old,
  const goto_programt &goto_program_old,
  const std::string &description_old,
  const std::string &path_prefix,
  const source_locationt &location,
  const goto_programt &goto_program,
  const std::string &description,
  const propertiest &properties,
  std::ostream &,
  message_handlert &);

#endif
