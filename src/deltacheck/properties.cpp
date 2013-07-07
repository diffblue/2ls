/*******************************************************************\

Module: Property Management

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "properties.h"
#include "html_escape.h"

/*******************************************************************\

Function: html_report

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void html_report(
  const propertiest &properties,
  std::ostream &out)
{
  out << "<table class=\"properties\">\n";

  out << "<tr>"
      << "<th>Status</th>\n"
      << "<th colspan=2>Location</th>\n"
      << "<th colspan=2>Property</th>\n"
      << "</tr>\n\n";

  for(propertiest::const_iterator
      p_it=properties.begin();
      p_it!=properties.end();
      p_it++)
  {
    const locationt &location=p_it->loc->location;
  
    out << "<tr class=\"property\""
           " onMouseOver=\"property(this,'over');\""
           " onMouseOut=\"property(this,'out');\""
           " onClick=\"property(this,'click');\""
           ">\n";
    
    out << "  <td align=\"center\">";
    
    if(p_it->status.is_false())
      out << "<font size=+1 color=\"#CC0000\">&#x2717;</font>" // ✗
             "</td> <!-- fail -->\n";
    else if(p_it->status.is_true())
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

