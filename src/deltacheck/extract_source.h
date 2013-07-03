/*******************************************************************\

Module: Extract Source for HTML

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_EXTRACT_SOURCE_H
#define CPROVER_EXTRACT_SOURCE_H

#include <ostream>

#include <util/location.h>

void extract_source(
  const locationt &begin, const locationt &end,
  std::ostream &);

#endif
