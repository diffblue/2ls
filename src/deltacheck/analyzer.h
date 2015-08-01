/*******************************************************************\

Module: Main Checker Interface

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_DELTACHECK_CHECKER_H
#define CPROVER_DELTACHECK_CHECKER_H

#include <util/options.h>

#include <goto-programs/goto_model.h>

class message_handlert;

void deltacheck_analyzer(
  const std::string &path1,
  const goto_modelt &goto_model1,
  const std::string &path2,
  const goto_modelt &goto_model2,
  const optionst &options,
  message_handlert &);

#endif
