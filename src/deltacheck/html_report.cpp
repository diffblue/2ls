/*******************************************************************\

Module: Indexing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "../html/html_escape.h"
#include "../html/logo.h"
#include "html_report.h"
#include "version.h"

/*******************************************************************\

Function: html_report_header

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const char header[]=
#include "report_header.inc"
;

void html_report_header(
  const std::string &title,
  std::ostream &out)
{
  out << "<!DOCTYPE html>\n<html>\n";

  out << "<head>\n";
  
  out << "<title>" << html_escape(title) << "</title>\n\n";

  out << header;

  out << "<head>\n";

  out << "\n"
         "<body>\n";
}

/*******************************************************************\

Function: html_report_header

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void html_report_header(
  std::ostream &out,
  const indext &index1, const indext &index2,
  const std::string &title)
{
  html_report_header(title, out);

  out << "<img src=\"" << deltacheck_logo
      << "\" class=\"image-right\" alt=\"DeltaCheck Logo\">\n\n";

  out << "<h1>" << html_escape(title) << "</h1>\n\n";

  out << "<p>DeltaCheck version: " << DELTACHECK_VERSION << "</p>\n";
  
  out << "<h2>Software under analysis</h2>\n";

  out << "<p><table>\n"
      << "<tr><td>Old version:</td><td>" << html_escape(index1.file_name)
      << "</td><td>" << html_escape(index1.description) << "</td></tr>\n";
  out << "<tr><td>New version:</td><td>" << html_escape(index2.file_name)
      << "</td><td>" << html_escape(index2.description) << "</td></tr>\n"
      << "</table></p>\n";
}

/*******************************************************************\

Function: html_report_header

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void html_report_header(
  std::ostream &out,
  const indext &index,
  const std::string &title)
{
  html_report_header(title, out);

  out << "<img src=\"" << deltacheck_logo
      << "\" class=\"image-right\" alt=\"DeltaCheck Logo\">\n\n";

  out << "<h1>" << html_escape(title) << "</h1>\n\n";

  out << "<p>DeltaCheck version: " << DELTACHECK_VERSION << "</p>\n";
  
  out << "<h2>Software under analysis</h2>\n";
  out << "<p>Single version: " << html_escape(index.file_name)
      << " " << html_escape(index.description) << "</p>\n";
}

/*******************************************************************\

Function: html_report_footer

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void html_report_footer(std::ostream &out)
{
  out << "<hr>\n"
         "\n"
         "<div class=\"copyright\">\n"
         "DeltaCheck is &copy; 2011&ndash;2013 Daniel Kroening, University of Oxford.\n"
         "</div>\n"
         "\n"
         "</body>\n"
         "</html>\n";
}
