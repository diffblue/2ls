/*******************************************************************\

Module: Collation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <fstream>
#include <set>

#include <goto-programs/show_claims.h>
#include <xmllang/xml_parser.h>

#include "reporting.h"
#include "get_goto_program.h"
#include "call_graph.h"

/*******************************************************************\

Function: get_functions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void get_functions(const xmlt &xml, std::set<irep_idt> &dest)
{
  xmlt::elementst::const_iterator functions=xml.find("functions");
  
  if(functions!=xml.elements.end())
  {
    for(xmlt::elementst::const_iterator
        f_it=functions->elements.begin();
        f_it!=functions->elements.end();
        f_it++)
    {
      dest.insert(f_it->get_attribute("id"));
    }
  }
}

/*******************************************************************\

Function: collate

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void collate(
  const std::vector<std::string> &files,
  const optionst &options,
  message_handlert &message_handler)
{
  
}

/*******************************************************************\

Function: call_graph_dot

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void call_graph_dot(
  const std::list<std::string> &files,
  const std::string &dest_file,
  message_handlert &message_handler)
{
  messaget message(message_handler);
  call_grapht call_graph;
  
  for(std::list<std::string>::const_iterator
      it=files.begin();
      it!=files.end();
      it++)
  {
    xmlt xml;
    if(parse_xml(*it+".summary", message_handler, xml))
      message.warning("failed to read summary of "+*it);
      
    summary_to_call_graph(xml, call_graph);
  }
  
  {
    message.status("Writing call graph");
    std::ofstream out(dest_file.c_str());
    if(!out)
      throw "failed to write call graph DOT";
    call_graph.output_dot(out);
    return;
  }
}

/*******************************************************************\

Function: reporting_cmdline

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void reporting_cmdline(
  const std::string &file_name,
  const optionst &options,
  message_handlert &message_handler)
{
  messaget message(message_handler);

  // get the goto program
  symbol_tablet symbol_table;
  goto_functionst goto_functions;
      
  get_goto_program(file_name, options, symbol_table, goto_functions, message_handler);

  namespacet ns(symbol_table);

  show_claims(ns, ui_message_handlert::PLAIN, goto_functions);
}
    
/*******************************************************************\

Function: reporting_cmdline

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void reporting_cmdline(
  const std::list<std::string> &files,
  const optionst &options,
  message_handlert &message_handler)
{
  if(options.get_option("call-graph-dot")!="")
  {
    call_graph_dot(files, options.get_option("call-graph-dot"),
                   message_handler);
    return;
  }
    
  // report status of claims on a per-file basis

  for(std::list<std::string>::const_iterator
      it=files.begin();
      it!=files.end();
      it++)
    reporting_cmdline(*it, options, message_handler);
}

/*******************************************************************\

Function: reporting_html

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void reporting_html(
  const std::string &file_name,
  const optionst &options,
  message_handlert &message_handler)
{
  #if 0
  messaget message(message_handler);

  // get the goto program
  symbol_tablet symbol_table;
  goto_functionst goto_functions;
      
  get_goto_program(file_name, options, symbol_table, goto_functions, message_handler);

  namespacet ns(symbol_table);

  show_claims(ns, ui_message_handlert::PLAIN, goto_functions);
  #endif
}
    
/*******************************************************************\

Function: reporting_html

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void reporting_html(
  const std::list<std::string> &files,
  const optionst &options,
  message_handlert &message_handler)
{
  if(options.get_option("call-graph-dot")!="")
    call_graph_dot(files, options.get_option("call-graph-dot"),
                   message_handler);
    
  // report status of claims on a per-file basis

  for(std::list<std::string>::const_iterator
      it=files.begin();
      it!=files.end();
      it++)
    reporting_html(*it, options, message_handler);
}

