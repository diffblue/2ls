/*******************************************************************\

Module: Indexing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "html_report.h"
#include "logo.h"
#include "version.h"
#include "html_escape.h"

/*******************************************************************\

Function: html_report_header

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void html_report_header(std::ostream &out)
{
  out << "<html>\n"
         "<head>\n";
  
  out << "<meta http-equiv=\"Content-Type\" content=\"text/html; charset=utf-8\">\n"
         "\n";
         
  out << "<style media=\"screen\" type=\"text/css\">\n"
         ".image-right { float: right; margin-left: 10px; }\n"
         "table.assertions { border-collapse:collapse; }\n"
         "table.assertions td, th { border:1px solid black; padding: 4px 4px 4px 8px; }\n"
         "p.function_statistics { font: 11px \"Trebuchet MS\", Verdana, Arial, Helvetica, sans-serif; }\n"
         "table.source td.line_numbers { text-align:right; }\n"
         "copyright { font: 9px \"Trebuchet MS\", Verdana, Arial, Helvetica, sans-serif; }\n"
         "</style>\n"
         "\n";

  out << "</head>\n"
         "\n"
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
  const indext &index1, const indext &index2)
{
  html_report_header(out);

  out << "<img src=\"" << deltacheck_logo
      << "\" class=\"image-right\" alt=\"DeltaCheck Logo\">\n\n";

  out << "<h1>DeltaCheck Report</h1>\n\n";

  out << "<p>DeltaCheck version: " << DELTACHECK_VERSION << "</p>\n";
  
  out << "<h2>Software under analysis</h2>\n";
  out << "<p>Old version: " << html_escape(index1.file_name)
      << " " << html_escape(index1.description) << "</p>\n";
  out << "<p>New version: " << html_escape(index2.file_name)
      << " " << html_escape(index2.description) << "</p>\n";
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
  html_report_header(out);

  out << "<img src=\"" << deltacheck_logo
      << "\" class=\"image-right\" alt=\"DeltaCheck Logo\">\n\n";

  out << "<h1>DeltaCheck Report</h1>\n\n";

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
  out << "<div class=\"copyright\">\n"
         "DeltaCheck is Copyright 2011&ndash;2013 Daniel Kroening, University of Oxford.\n"
         "</div>\n"
         "</body>\n"
         "</html>\n";
}
