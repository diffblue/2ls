/*******************************************************************\

Module: Indexing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <fstream>

#include <util/message.h>
#include <goto-programs/read_goto_binary.h>
#include <goto-programs/goto_model.h>

#include "index.h"
#include "function_delta.h"
#include "html_report.h"
#include "get_function.h"
#include "simple_check.h"

/*******************************************************************\

Function: simple_check_function

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void simple_check_function(
  const irep_idt &id,
  const goto_functionst::goto_functiont &f,
  std::ostream &report,
  message_handlert &message_handler)          
{
  const goto_functionst::goto_functiont f_empty;
  function_delta(id, f_empty, f, report, message_handler);
}

/*******************************************************************\

Function: simple_check_function

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void simple_check_function(
  const indext &index,
  const std::string &function,
  std::ostream &report,
  message_handlert &message_handler)
{
  const irep_idt id="c::"+function;

  get_functiont get_function(index);
  get_function.set_message_handler(message_handler);
  
  messaget message(message_handler);
  
  const goto_functionst::goto_functiont *index_fkt=
    get_function(id);
  
  if(index_fkt==NULL)
  {
    message.error("function \""+function+"\" not found in index");
    return;
  }

  simple_check_function(id, *index_fkt, report, message_handler);
}

/*******************************************************************\

Function: simple_check_all

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void simple_check_all(
  const indext &index,
  std::ostream &report,
  message_handlert &message_handler)
{
  // we do this by file in the index
  
  messaget message(message_handler);

  for(indext::filest::const_iterator
      file_it=index.files.begin();
      file_it!=index.files.end();
      file_it++)
  {
    message.status("Processing \""+id2string(*file_it)+"\"");
    
    // read the file
    goto_modelt model;
    read_goto_binary(id2string(*file_it), model, message_handler);
    
    const std::set<irep_idt> &functions=
      index.file_to_function.find(*file_it)->second;

    // now do all functions from model
    for(std::set<irep_idt>::const_iterator
        fkt_it=functions.begin();
        fkt_it!=functions.end();
        fkt_it++)
    {
      const irep_idt &id=*fkt_it;
      const goto_functionst::goto_functiont *index_fkt=
        &model.goto_functions.function_map.find(id)->second;
    
      message.status("Checking \""+id2string(id)+"\"");
      
      report << "<h2>Function " << id << " in " << *file_it
             << "</h2>" << std::endl;
      
      simple_check_function(id, *index_fkt, report, message_handler);
    }
  }
}

/*******************************************************************\

Function: simple_check

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void simple_check(
  const indext &index,
  const std::string &function,
  message_handlert &message_handler)
{
  std::string report_file_name="deltacheck.html";
  std::ofstream out(report_file_name.c_str());

  if(!out)
  {
    messaget message(message_handler);
    message.error() << "failed to write to \""
                    << report_file_name << "\"" << messaget::eom;
    return;
  }

  html_report_header(out, index);

  if(function=="")
    simple_check_all(index, out, message_handler);
  else
    simple_check_function(index, function, out, message_handler);

  html_report_footer(out, index);
}

