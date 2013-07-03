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
#include "html_escape.h"
#include "statistics.h"

class one_program_checkt:public messaget
{
public:
  one_program_checkt(
    const indext &_index,
    std::ostream &_report,
    message_handlert &message_handler):
    messaget(message_handler),
    index(_index),
    report(_report)
  {
  }
  
  const indext &index;
  std::ostream &report;
  statisticst statistics;
  optionst options;
  
  void check_function(const std::string &);
  void check_all();

protected:

  void check_function(
    const irep_idt &id,
    goto_functionst::goto_functiont &f,
    const namespacet &ns);
};

/*******************************************************************\

Function: one_program_checkt::check_function

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void one_program_checkt::check_function(
  const irep_idt &id,
  goto_functionst::goto_functiont &f,
  const namespacet &ns)
{
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
  status() << "Generating properties" << eom;
  goto_check(ns, options, f);

  // build SSA
  fine_timet start_ssa=current_time();
  status() << "Building SSA" << eom;
  function_SSAt function_SSA(f, ns);
  
  // now do fixed-point
  fine_timet start_fp=current_time();
  status() << "Data-flow fixed-point" << eom;
  ssa_data_flowt ssa_data_flow(function_SSA);
  
  // now report on assertions
  fine_timet start_reporting=current_time();
  status() << "Reporting" << eom;
  report_assertions(ssa_data_flow, report);
  fine_timet end_reporting=current_time();
  
  // dump statistics
  statistics.html_report_function(report);
}

/*******************************************************************\

Function: one_program_checkt::check_function

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void one_program_checkt::check_function(const std::string &function)
{
  const irep_idt id="c::"+function;

  get_functiont get_function(index);
  get_function.set_message_handler(get_message_handler());
  
  const namespacet &ns=get_function.ns;
  
  goto_functionst::goto_functiont *index_fkt=
    get_function(id);
  
  if(index_fkt==NULL)
  {
    error() << "function \"" << function
            << "\" not found in index" << eom;
    return;
  }

  check_function(id, *index_fkt, ns);
}

/*******************************************************************\

Function: one_program_checkt::check_all

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void one_program_checkt::check_all()
{
  // we do this by file in the index
  
  for(indext::file_to_functiont::const_iterator
      file_it=index.file_to_function.begin();
      file_it!=index.file_to_function.end();
      file_it++)
  {
    status() << "Processing \"" << file_it->first << "\"" << eom;
    
    // read the file
    goto_modelt model;
    read_goto_binary(id2string(file_it->first), model, get_message_handler());
   
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
        error() << "failed to find function `" << id2string(id)
                << "'" << eom;
        continue;
      }
      
      goto_functionst::goto_functiont *index_fkt=
        &fmap_it->second;
    
      status() << "Checking \"" << id2string(id) << "\"" << eom;
      
      const symbolt &symbol=ns.lookup(id);

      report << "<h2>Function " << html_escape(symbol.display_name())
             << " in " << html_escape(file_it->first)
             << "</h2>\n";

      check_function(id, *index_fkt, ns);
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
  std::string report_file_name="deltacheck.html";
  std::ofstream out(report_file_name.c_str());
  
  messaget message(message_handler);

  if(!out)
  {
    message.error() << "failed to write to \""
                    << report_file_name << "\"" << messaget::eom;
    return;
  }
  
  message.status() << "Writing report into \""
                   << report_file_name << "\"" << messaget::eom;

  html_report_header(out, index);

  one_program_checkt opc(index, out, message_handler);
  
  if(function=="")
    opc.check_all();
  else
    opc.check_function(function);

  html_report_footer(out, index);
}  
