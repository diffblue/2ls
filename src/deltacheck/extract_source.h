/*******************************************************************\

Module: Extract Source for HTML

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_EXTRACT_SOURCE_H
#define CPROVER_EXTRACT_SOURCE_H

#include <ostream>

#include <util/message.h>
#include <goto-programs/goto_functions.h>

#include "properties.h"

void extract_source(
  const locationt &location,
  const goto_programt &goto_program,
  const propertiest &properties,
  std::ostream &,
  message_handlert &);

void extract_source(
  const locationt &location_old,
  const goto_programt &goto_program_old,
  const locationt &location,
  const goto_programt &goto_program,
  const propertiest &properties,
  std::ostream &,
  message_handlert &);

#endif
