/*******************************************************************\

Module: Call Graph

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "call_graph.h"

/*******************************************************************\

Function: call_grapht::add_summary

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void call_grapht::add_summary(const xmlt &xml)
{
  xmlt::elementst::const_iterator functions=xml.find("functions");
  
  if(functions!=xml.elements.end())
  {
    for(xmlt::elementst::const_iterator
        f_it=functions->elements.begin();
        f_it!=functions->elements.end();
        f_it++)
    {
      std::pair<irep_idt, irep_idt> entry;
      entry.first=f_it->get_attribute("id");

      for(xmlt::elementst::const_iterator
          c_it=f_it->elements.begin();
          c_it!=f_it->elements.end();
          c_it++)
      {
        if(c_it->name=="called")
        {
          entry.second=c_it->get_attribute("id");
          insert(entry);
        }
      }
    }
  }
}

/*******************************************************************\

Function: call_grapht::output_dot

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void call_grapht::output_dot(std::ostream &out) const
{
  out << "digraph call_graph {" << std::endl;

  for(const_iterator it=begin();
      it!=end();
      it++)
  {
    out << "  \"" << it->first << "\" -> "
        << "\"" << it->second << "\" "
        << " [arrowhead=\"vee\"];"
        << std::endl;
  }
  
  out << "}" << std::endl;
}

