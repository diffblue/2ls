/*******************************************************************\

Module: Summarization

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_DELTACHECK_SUMMARIZATION_H
#define CPROVER_DELTACHECK_SUMMARIZATION_H

#include <options.h>
#include <context.h>

#include <goto-programs/goto_functions.h>

void summarization(
  const std::string &file_name,
  const contextt &,
  const goto_functionst &,
  const optionst &);

#endif
