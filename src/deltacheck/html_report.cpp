/*******************************************************************\

Module: Indexing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "html_report.h"
#include "logo.h"
#include "version.h"

/*******************************************************************\

Function: html_report_header

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void html_report_header(
  std::ostream &out,
  const indext &index1, const indext &index2)
{
  out << "<html>\n"
         "<head>\n"
         "</head>\n"
         "\n"
         "<body>\n";

  out << "<h1>DeltaCheck Report</h1>\n\n";
  out << "<img src=\"" << deltacheck_logo
      << "\" class=\"image-right\" alt=\"DeltaCheck Logo\">\n\n";
  out << "<p>DeltaCheck version: " << DELTACHECK_VERSION << "</p>\n";
  
  out << "<h2>Software under analysis</h2>\n";
  out << "<p>Old version: " << index1.file_name << " " << index1.description << "</p>\n";
  out << "<p>New version: " << index2.file_name << " " << index2.description << "</p>\n";
}

/*******************************************************************\

Function: html_report_header

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void html_report_header(
  std::ostream &out,
  const indext &index)
{
  out << "<html>\n"
         "<head>\n"
         "</head>\n"
         "\n"
         "<body>\n";

  out << "<h1>DeltaCheck Report</h1>\n\n";
  out << "<img src=\"" << deltacheck_logo
      << "\" class=\"image-right\" alt=\"DeltaCheck Logo\">\n\n";
  out << "<p>DeltaCheck version: " << DELTACHECK_VERSION << "</p>\n";
  
  out << "<h2>Software under analysis</h2>\n";
  out << "<p>Single version: " << index.file_name << " " << index.description << "</p>\n";
}

/*******************************************************************\

Function: html_report_footer

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void html_report_footer(
  std::ostream &out,
  const indext &index1, const indext &index2)
{
  out << "</body>\n"
         "</html>\n";
}

/*******************************************************************\

Function: html_report_footer

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void html_report_footer(
  std::ostream &out,
  const indext &index)
{
  out << "</body>\n"
         "</html>\n";
}
