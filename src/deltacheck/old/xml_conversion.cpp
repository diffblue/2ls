/*******************************************************************\

Module: 

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "xml_conversion.h"

/*******************************************************************\

Function: xml

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

#if 0
xmlt xml(const locationt &location)
{
  xmlt xml_location;
  xml_location.name="location";

  if(location.get_file()!="")
    xml_location.set_attribute("file", id2string(location.get_file()));
    
  if(location.get_line()!="")
    xml_location.set_attribute("line", id2string(location.get_line()));

  return xml_location;
}
#endif
