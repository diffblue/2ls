/*******************************************************************\

Module: Set up a new repository

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_DELTAREPO_INIT_H
#define CPROVER_DELTAREPO_INIT_H

#include <string>

enum repo_kindt { NONE, GIT, SVN };

void init(
  repo_kindt repo_kind,
  const std::string &url,
  const std::string &dest);

#endif
