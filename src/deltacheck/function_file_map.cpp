/*******************************************************************\

Module: Map from function names to the file

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <xmllang/xml_parser.h>

#include "function_file_map.h"

/*******************************************************************\

Function: build_function_file_map

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void build_function_file_map(
  const std::list<std::string> &files,
  message_handlert &message_handler,
  function_file_mapt &function_file_map)
{
  for(std::list<std::string>::const_iterator
      file_it=files.begin();
      file_it!=files.end();
      file_it++)
  {
    xmlt xml;
    parse_xml(*file_it+".summary", message_handler, xml);
    
    irep_idt file=*file_it;

    xmlt::elementst::const_iterator functions=xml.find("functions");
  
    if(functions!=xml.elements.end())
    {
      for(xmlt::elementst::const_iterator
          f_it=functions->elements.begin();
          f_it!=functions->elements.end();
          f_it++)
      {
        irep_idt id=f_it->get_attribute("id");
        function_file_map[id]=file;
      }
    }
  }
}
