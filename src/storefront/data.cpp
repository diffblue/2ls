/*******************************************************************\

Module: Trace View

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/cout_message.h>
#include <util/string2int.h>

#include <xmllang/xml_parser.h>

#include "data.h"

/*******************************************************************\

Function: datat::read

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void datat::read(const std::string &file)
{
  xmlt xml;

  console_message_handlert message_handler;
  parse_xml(file, message_handler, xml);

  read(xml);
}

/*******************************************************************\

Function: datat::read

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void datat::read(const xmlt &xml)
{
  for(xmlt::elementst::const_iterator
      it=xml.elements.begin();
      it!=xml.elements.end();
      it++)
  {
    if(it->name=="property")
    {
      propertyt property;
    
      for(xmlt::elementst::const_iterator
          e_it=it->elements.begin();
          e_it!=it->elements.end();
          e_it++)
      {
        if(e_it->name=="file")
          property.file=e_it->data;
        else if(e_it->name=="line")
          property.line=unsafe_string2unsigned(e_it->data);
        else if(e_it->name=="category")
          property.category=e_it->data;
        else if(e_it->name=="message")
          property.message=e_it->data;
      }
      
      properties.push_back(property);
    }
    else if(it->name=="description")
    {
      description=it->data;
    }
  }
}

