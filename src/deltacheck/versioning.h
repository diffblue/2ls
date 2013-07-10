/*******************************************************************\

Module: Delta Check an SVN Repository

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef DELTACHECK_VERSIONING_H
#define DELTACHECK_VERSIONING_H

#include <string>

#include <util/message.h>

void svn(const std::string &url,
         const std::string &revision,
         message_handlert &);

void git(const std::string &url,
         const std::string &revision,
         message_handlert &);

#endif
