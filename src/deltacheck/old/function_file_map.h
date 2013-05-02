/*******************************************************************\

Module: Map from function names to the file

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_DELTACHECK_FUNCTION_FILE_MAP_H
#define CPROVER_DELTACHECK_FUNCTION_FILE_MAP_H

#include <map>

#include <util/irep.h>

typedef std::map<irep_idt, irep_idt> function_file_mapt;

void build_function_file_map(
  const std::list<std::string> &files,
  class message_handlert &message_handler,
  function_file_mapt &function_file_map);

#endif
