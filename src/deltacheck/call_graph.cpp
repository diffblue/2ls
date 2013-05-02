/*******************************************************************\

Module: Call Graph

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "call_graph.h"

/*******************************************************************\

Function: summary_to_call_graph

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summary_to_call_graph(const xmlt &xml, call_grapht &dest)
{
  xmlt::elementst::const_iterator functions=xml.find("functions");
  
  if(functions!=xml.elements.end())
  {
    for(xmlt::elementst::const_iterator
        f_it=functions->elements.begin();
        f_it!=functions->elements.end();
        f_it++)
    {
      irep_idt caller=f_it->get_attribute("id");

      for(xmlt::elementst::const_iterator
          c_it=f_it->elements.begin();
          c_it!=f_it->elements.end();
          c_it++)
      {
        if(c_it->name=="called")
        {
          irep_idt callee=c_it->get_attribute("id");
          dest.add(caller, callee);
        }
      }
    }
  }
}
