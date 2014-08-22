/*******************************************************************\

Module: Job Status

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <fstream>

#include <util/xml.h>
#include <util/cout_message.h>

#include <xmllang/xml_parser.h>

#include "deltagit_config.h"

/*******************************************************************\

Function: deltagit_configt::read

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void deltagit_configt::read()
{
  xmlt src;
  
  console_message_handlert message_handler;
      
  if(parse_xml("config.xml", message_handler, src))
    return;

  if(src.name!="deltagit_config")
    throw std::string("unexpected XML for deltagit config");

  description=src.get_element("description");
}

