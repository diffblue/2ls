/*******************************************************************\

Module: Dependency Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <fstream>

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
  std::string summary_file=file_name+".summary";
  
  std::ifstream in(summary_file.c_str());

  if(!in) return STALE;
  
  xmlt xml;
  parse_xml(in, summary_file, message_handler, xml);
  
  return STALE;
}
