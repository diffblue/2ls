/*******************************************************************\

Module: Read Configuration File

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <string>

#include <util/cout_message.h>
#include <xmllang/xml_parser.h>

#include "deltarepo_config.h"

/*******************************************************************\

Function: deltarepo_configt::deltarepo_configt

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

deltarepo_configt::deltarepo_configt()
{
  console_message_handlert message_handler;
  xmlt xml;

  if(parse_xml(file_name(), message_handler, xml))
    throw std::string("failed to parse XML from SVN");

  if(xml.name!="info")
    throw std::string("unexpected XML from svn");

  std::string kind_string=xml.get_attribute("kind");

  if(kind_string=="git")
    kind=GIT;    
  else if(kind_string=="svn")
    kind=SVN;    
  else
    throw std::string("repository of unknown kind");

  url=xml.get_attribute("url");
}
