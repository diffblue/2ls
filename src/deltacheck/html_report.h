/*******************************************************************\

Module: Delta Check HTML Reporting

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_HTML_REPORT_H
#define CPROVER_HTML_REPORT_H

#include <ostream>

#include <goto-programs/goto_model.h>

void html_report_header(
  std::ostream &out,
  const std::string &old_desc, const std::string &new_desc,
  const std::string &title);

void html_report_header(
  const std::string &title,
  std::ostream &out);

void html_report_footer(std::ostream &out);

#endif
