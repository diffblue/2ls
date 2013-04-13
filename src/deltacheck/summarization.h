/*******************************************************************\

Module: Summarization

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_DELTACHECK_SUMMARIZATION_H
#define CPROVER_DELTACHECK_SUMMARIZATION_H

#include <util/options.h>
#include <util/symbol_table.h>
#include <util/message.h>

#include "function_file_map.h"

void summarization(
  const function_file_mapt &function_file_map,
  const std::string &file_name,
  const optionst &,
  message_handlert &);

#endif
