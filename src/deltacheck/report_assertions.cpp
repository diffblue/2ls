/*******************************************************************\

Module: Reporting

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "report_assertions.h"
#include "html_escape.h"

/*******************************************************************\

Function: report_assertions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void report_assertions(
  const ssa_data_flowt &ssa_data_flow,
  std::ostream &out)
{
  out << "<table class=\"assertions\">\n";

  out << "<tr>"
      << "<th>Status</th>\n"
      << "<th colspan=2>Location</th>\n"
      << "<th colspan=2>Property</th>\n"
      << "</tr>\n\n";

  for(ssa_data_flowt::assertionst::const_iterator
      a_it=ssa_data_flow.assertions.begin();
      a_it!=ssa_data_flow.assertions.end();
      a_it++)
  {
    const locationt &location=a_it->loc->location;
  
    out << "<tr>\n";
    
    out << "  <td align=\"center\">";
    
    if(a_it->status.is_false())
      out << "<font size=+1 color=\"#CC0000\">&#x2717;</font>" // ✗
             "</td> <!-- fail -->\n";
    else if(a_it->status.is_true())
      out << "<font size=+1 color=\"#009933\">&#x2713;</font>"
             "</td> <!-- pass -->\n"; // ✓
    else
      out << "<font size=+1 color=\"#FFCC00\">?</font>"
             "</td> <!-- unknown -->\n";
    
    out << "  <td>";
    out << html_escape(location.get_file());
    out << "</td>\n";

    out << "  <td>";
    out << html_escape(location.get_line());
    out << "</td>\n";
    
    out << "  <td>";
    out << html_escape(location.get_property());
    out << "</td>\n";
    
    out << "  <td>";
    out << html_escape(location.get_comment());
    out << "</td>\n";
    
    out << "</tr>\n\n";
  }
  
  out << "</table>\n";
}

