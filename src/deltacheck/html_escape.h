/*******************************************************************\

Module: Delta Check HTML Reporting

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef DELTACHECK_HTML_ESCAPE
#define DELTACHECK_HTML_ESCAPE

#include <util/dstring.h>

#include <string>

std::string html_escape(const std::string &);
std::string html_escape(const dstring &);

#endif
