/*******************************************************************\

Module: Dependency Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_DELTACHECK_DEPENDENCIES_H
#define CPROVER_DELTACHECK_DEPENDENCIES_H

#include <util/options.h>

#include "function_file_map.h"

typedef enum { STALE, FRESH } dependency_statet;

dependency_statet dependencies(
  const function_file_mapt &function_file_map,
  const std::string &file_name,
  class message_handlert &message_handler);

#endif
