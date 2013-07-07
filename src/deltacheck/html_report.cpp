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
  
  // CSS       
  out << "<style media=\"screen\" type=\"text/css\">\n";
  
  // logo
  out << ".image-right { float: right; margin-left: 10px; }\n";

  // Table of files
  out << "table.file-table { border-collapse:collapse; }\n"
         "table.file-table td, th { border:1px solid black; padding: 2px 2px 2px 4px; }\n";
         
  // Table of properties         
  out << "table.properties { border-collapse:collapse; }\n"
         "table.properties td, th { border:1px solid black; padding: 4px 4px 4px 8px; }\n";
         
  // Small stuff
  out << "p.function_statistics { font: 11px \"Trebuchet MS\", Verdana, Arial, Helvetica, sans-serif; }\n"
         ".copyright { font: 9px \"Trebuchet MS\", Verdana, Arial, Helvetica, sans-serif; }\n";
        
  // Source code formatting 
  out << "table.source td.line_numbers { text-align:right; }\n"
         "em { font-style: normal; font-weight:bold; }\n"
         "cite { font-style: normal; color: #4e9a06; }\n"
         "strong.different { font-style: normal; background-color: #fce94f; font-weight: normal; }\n";

  out << "</style>\n"
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
  out << "<hr>\n"
         "\n"
         "<div class=\"copyright\">\n"
         "DeltaCheck is Copyright 2011&ndash;2013 Daniel Kroening, University of Oxford.\n"
         "</div>\n"
         "\n"
         "</body>\n"
         "</html>\n";
}
