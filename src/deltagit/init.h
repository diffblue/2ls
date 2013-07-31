/*******************************************************************\

Module: Set up a new repository

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_DELTAREPO_INIT_H
#define CPROVER_DELTAREPO_INIT_H

#include "deltarepo_config.h"

void check(
  repo_kindt repo_kind,
  const std::string &url);

void init(
  repo_kindt repo_kind,
  const std::string &url,
  const std::string &dest);

#endif
