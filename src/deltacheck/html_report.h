/*******************************************************************\

Module: Delta Check HTML Reporting

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_HTML_REPORT_H
#define CPROVER_HTML_REPORT_H

#include <ostream>

#include "../functions/index.h"

void html_report_header(
  std::ostream &out,
  const indext &index1, const indext &index2,
  const std::string &title);

void html_report_header(
  std::ostream &out,
  const indext &index1,
  const std::string &title);

void html_report_footer(std::ostream &out);

#endif
