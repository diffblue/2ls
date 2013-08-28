/*******************************************************************\

Module: Delta Check HTML Reporting

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "html_escape.h"

/*******************************************************************\

Function: html_escape

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string html_escape(const std::string &src)
{
  std::string result;
  
  result.reserve(src.size());
  
  for(unsigned i=0; i<src.size(); i++)
    switch(src[i])
    {
    case '<': result+="&lt;"; break;
    case '>': result+="&gt;"; break;
    case '"': result+="&quot;"; break;
    case '\'': result+="&apos;"; break;
    case '&': result+="&amp;"; break;
    default: result+=src[i];
    }
  
  return result;
}

/*******************************************************************\

Function: html_escape

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string html_escape(const dstring &src)
{
  return html_escape(as_string(src));
}
