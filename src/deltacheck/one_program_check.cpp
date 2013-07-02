/*******************************************************************\

Module: Indexing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <fstream>

#include <util/message.h>
#include <util/time_stopping.h>

#include <goto-programs/read_goto_binary.h>
#include <goto-programs/goto_model.h>
#include <analyses/goto_check.h>

#include "index.h"
#include "html_report.h"
#include "get_function.h"
#include "one_program_check.h"
#include "ssa_data_flow.h"
#include "report_assertions.h"

/*******************************************************************\

Function: one_program_check_function

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void one_program_check_function(
  const irep_idt &id,
  goto_functionst::goto_functiont &f,
  const namespacet &ns,
  std::ostream &report,
  message_handlert &message_handler)
{
  messaget message(message_handler);
  
  optionst options;
  options.set_option("bounds-check", true);
  options.set_option("pointer-check", true);
  options.set_option("div-by-zero-check", true);
  options.set_option("signed-overflow-check", true);
  //options.set_option("unsigned-overflow-check", true);
  options.set_option("undefined-shift-check", true);
  //options.set_option("float-overflow-check", true);
  options.set_option("simplify", true);
  //options.set_option("nan-check", true);
  options.set_option("assertions", true);
  options.set_option("assumptions", true);

  // add properties
  fine_timet start_prop=current_time();
  message.status() << "Generating properties" << messaget::eom;
  goto_check(ns, options, f);

  // build SSA
  fine_timet start_ssa=current_time();
  message.status() << "Building SSA" << messaget::eom;
  function_SSAt function_SSA(f, ns);
  
  // now do fixed-point
  fine_timet start_fp=current_time();
  message.status() << "Data-flow fixed-point" << messaget::eom;
  ssa_data_flowt ssa_data_flow(function_SSA);
  
  // now report on assertions
  fine_timet start_reporting=current_time();
  message.status() << "Reporting" << messaget::eom;
  report_assertions(ssa_data_flow, report);
  fine_timet end_reporting=current_time();
  
  // dump statistics
  report << "<p class=\"statistics\">Properties: " << start_ssa-start_prop
         << "s SSA: " << start_fp-start_ssa
         << "s Fixed-point: " << start_reporting-start_fp
         << "s Reporting: " << start_reporting-end_reporting
         << "s</p>\n";
}

/*******************************************************************\

Function: one_program_check_function

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void one_program_check_function(
  const indext &index,
  const std::string &function,
  std::ostream &report,
  message_handlert &message_handler)
{
  const irep_idt id="c::"+function;

  get_functiont get_function(index);
  get_function.set_message_handler(message_handler);
  
  const namespacet &ns=get_function.ns;
  
  messaget message(message_handler);
  
  goto_functionst::goto_functiont *index_fkt=
    get_function(id);
  
  if(index_fkt==NULL)
  {
    message.error() << "function \"" << function
                    << "\" not found in index" << messaget::eom;
    return;
  }

  one_program_check_function(id, *index_fkt, ns, report, message_handler);
}

/*******************************************************************\

Function: one_program_check_all

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void one_program_check_all(
  const indext &index,
  std::ostream &report,
  message_handlert &message_handler)
{
  // we do this by file in the index
  
  messaget message(message_handler);

  for(indext::file_to_functiont::const_iterator
      file_it=index.file_to_function.begin();
      file_it!=index.file_to_function.end();
      file_it++)
  {
    message.status() << "Processing \"" << file_it->first << "\""
                     << messaget::eom;
    
    // read the file
    goto_modelt model;
    read_goto_binary(id2string(file_it->first), model, message_handler);
   
    const namespacet ns(model.symbol_table); 
    const std::set<irep_idt> &functions=file_it->second;

    // now do all functions from model
    for(std::set<irep_idt>::const_iterator
        fkt_it=functions.begin();
        fkt_it!=functions.end();
        fkt_it++)
    {
      const irep_idt &id=*fkt_it;
      
      const goto_functionst::function_mapt::iterator
        fmap_it=model.goto_functions.function_map.find(id);
        
      if(fmap_it==model.goto_functions.function_map.end())
      {
        message.error() << "failed to find function `" << id2string(id)
                        << "'" << messaget::eom;
        continue;
      }
      
      goto_functionst::goto_functiont *index_fkt=
        &fmap_it->second;
    
      message.status() << "Checking \"" << id2string(id) << "\""
                       << messaget::eom;
      
      report << "<h2>Function " << id << " in " << file_it->first
             << "</h2>" << std::endl;
      
      one_program_check_function(id, *index_fkt, ns, report, message_handler);
    }
  }
}

/*******************************************************************\

Function: one_program_check

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void one_program_check(
  const indext &index,
  const std::string &function,
  message_handlert &message_handler)
{
  messaget message(message_handler);

  std::string report_file_name="deltacheck.html";
  std::ofstream out(report_file_name.c_str());

  if(!out)
  {
    message.error() << "failed to write to \""
                    << report_file_name << "\"" << messaget::eom;
    return;
  }
  
  message.status() << "Writing report into \""
                   << report_file_name << "\"" << messaget::eom;

  html_report_header(out, index);

  if(function=="")
    one_program_check_all(index, out, message_handler);
  else
    one_program_check_function(index, function, out, message_handler);

  html_report_footer(out, index);
}

