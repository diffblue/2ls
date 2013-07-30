/*******************************************************************\

Module: Indexing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/xml.h>
#include <xmllang/xml_parser.h>

#include <goto-programs/read_goto_binary.h>
#include <goto-programs/goto_model.h>

#include "index.h"
#include "version.h"

/*******************************************************************\

Function: indext::build

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void indext::build(const std::vector<std::string> &files,
                   const std::string &_description)
{
  description=_description;
  path_prefix="";

  for(std::vector<std::string>::const_iterator
      f_it=files.begin();
      f_it!=files.end();
      f_it++)
    index_goto_binary(*f_it);
}              

/*******************************************************************\

Function: indext::write

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void indext::write(std::ostream &out) const
{
  out << "<?xml verion=\"1.0\" encoding=\"UTF-8\"?>\n";

  out << "<DeltaCheckIndex version=\""
      << DELTACHECK_VERSION << "\">\n";
  
  out << "<description>";
  xmlt::escape(description, out);
  out << "</description>\n";
  out << "\n";
  
  for(file_to_functiont::const_iterator
      it=file_to_function.begin();
      it!=file_to_function.end();
      it++)
  {
    out << "<file name=\"";
    xmlt::escape_attribute(id2string(it->first), out);
    out << "\">\n";

    const std::set<irep_idt> &functions=it->second;

    for(std::set<irep_idt>::const_iterator
        f_it=functions.begin(); f_it!=functions.end(); f_it++)
    {
      out << "  <function id=\"";
      xmlt::escape_attribute(id2string(*f_it), out);
      out << "\"/>\n";
    }    
    
    out << "</file>\n";
  }
  
  out << "</DeltaCheckIndex>\n";  
}

/*******************************************************************\

Function: indext::index_goto_binary

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void indext::index_goto_binary(const irep_idt &file)
{
  status() << "Reading `" << file << "'" << eom;
  
  goto_modelt goto_model;
  
  if(read_goto_binary(id2string(file), goto_model, get_message_handler()))
  {
    error() << "failed to read `" << file << "'" << eom;
    return;
  }
  
  // index the functions
  for(goto_functionst::function_mapt::const_iterator
      f_it=goto_model.goto_functions.function_map.begin();
      f_it!=goto_model.goto_functions.function_map.end();
      f_it++)
  {
    if(f_it->second.body_available)
    {
      function_to_file[f_it->first].insert(file);
      file_to_function[file].insert(f_it->first);
    }
  }    
}

/*******************************************************************\

Function: indext::read

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void indext::read(const std::string &in_file_name)
{
  file_name=in_file_name;
  
  {
    #ifdef _WIN32
    char path_sep='\\';
    #else
    char path_sep='/';
    #endif
    
    std::size_t path_sep_pos=in_file_name.rfind(path_sep);
    if(path_sep_pos!=std::string::npos)
      path_prefix=in_file_name.substr(0, path_sep_pos+1);
  }
  
  // figure out if this is a goto-binary or an index
  if(is_goto_binary(file_name))
  {
    index_goto_binary(file_name);
  }
  else
  {
    xmlt xml;
    parse_xml(in_file_name, get_message_handler(), xml);
    
    if(xml.name!="DeltaCheckIndex")
      return;

    description=xml.get_element("description");

    for(xmlt::elementst::const_iterator
        file_it=xml.elements.begin();
        file_it!=xml.elements.end();
        file_it++)
    {
      if(file_it->name!="file") continue;
    
      irep_idt file_name=file_it->get_attribute("name");
      
      // create map entry
      file_to_function[file_name];

      for(xmlt::elementst::const_iterator
          fkt_it=file_it->elements.begin();
          fkt_it!=file_it->elements.end();
          fkt_it++)
      {
        irep_idt function_id=fkt_it->get_attribute("id");
        function_to_file[function_id].insert(file_name);
        file_to_function[file_name].insert(function_id);
      }
    }
  }
}
