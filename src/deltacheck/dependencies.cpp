/*******************************************************************\

Module: Dependency Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <xmllang/xml_parser.h>

#include "dependencies.h"

/*******************************************************************\

Function: dependencies

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

dependency_statet dependencies(
  const function_file_mapt &function_file_map,
  const std::string &file_name,
  message_handlert &message_handler)
{
  xmlt xml;
  parse_xml(file_name+".summary", message_handler, xml);
  
  return STALE;
}
