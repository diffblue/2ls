/*******************************************************************\

Module: Delta Check HTML Reporting

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_HTML_REPORT_H
#define CPROVER_HTML_REPORT_H

#include <ostream>

#include "index.h"

void html_report_header(
  std::ostream &out,
  const indext &index1, const indext &index2);

void html_report_header(
  std::ostream &out,
  const indext &index1);

void html_report_footer(std::ostream &out);

#endif
