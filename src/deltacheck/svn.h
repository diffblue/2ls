/*******************************************************************\

Module: Delta Check an SVN Repository

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef DELTACHECK_SVN_H
#define DELTACHECK_SVN_H

#include <string>

#include <util/message.h>

void svn(const std::string &url,
         const std::string &revision,
         message_handlert &);

#endif
