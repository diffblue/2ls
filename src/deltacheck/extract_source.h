/*******************************************************************\

Module: Extract Source for HTML

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_EXTRACT_SOURCE_H
#define CPROVER_EXTRACT_SOURCE_H

#include <ostream>

#include <goto-programs/goto_functions.h>

void extract_source(
  const locationt &location,
  const goto_programt &goto_program,
  std::ostream &);

#endif
