/*******************************************************************\

Module: talk to SVN

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_DELTAREPO_DO_SVN_H
#define CPROVER_DELTAREPO_DO_SVN_H

#include <string>

class xmlt;

void do_svn(const std::string &, xmlt &);
void do_svn(const std::string &);

#endif
