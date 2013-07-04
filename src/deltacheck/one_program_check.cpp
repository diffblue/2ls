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
#include "extract_source.h"

class one_program_checkt:public messaget
{
public:
  one_program_checkt(
    const indext &_index,
    message_handlert &message_handler):
    messaget(message_handler),
    index(_index)
  {
  }
  
  const indext &index;
  statisticst statistics;
  optionst options;
  
  void check_all(std::ostream &global_report);

protected:

  void check_function(
    const symbolt &symbol,
    goto_functionst::goto_functiont &f,
    const namespacet &ns,
    std::ostream &file_report);
};

/*******************************************************************\

Function: one_program_checkt::check_function

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void one_program_checkt::check_function(
  const symbolt &symbol,
  goto_functionst::goto_functiont &f,
  const namespacet &ns,
  std::ostream &file_report)
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
  
  statistics.next_function();

  // add properties
  status() << "Generating properties" << eom;
  statistics.start("Properties");
  goto_check(ns, options, f);
  statistics.stop("Properties");

  // build SSA
  status() << "Building SSA" << eom;
  statistics.start("SSA");
  function_SSAt function_SSA(f, ns);
  statistics.stop("SSA");
  
  // now do fixed-point
  status() << "Data-flow fixed-point" << eom;
  statistics.start("Fixed-point");
  ssa_data_flowt ssa_data_flow(function_SSA);
  statistics.stop("Fixed-point");
  
  // now report on assertions
  status() << "Reporting" << eom;
  statistics.start("Reporting");
  report_assertions(ssa_data_flow, file_report);
  extract_source(symbol.location, f.body, file_report);
  statistics.stop("Reporting");
  
  // dump statistics
  statistics.html_report_function(file_report);
}

/*******************************************************************\

Function: one_program_checkt::check_all

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void one_program_checkt::check_all(std::ostream &global_report)
{
  // we do this by file in the index
  
  for(indext::file_to_functiont::const_iterator
      file_it=index.file_to_function.begin();
      file_it!=index.file_to_function.end();
      file_it++)
  {
    status() << "Processing \"" << file_it->first << "\"" << eom;
    
    std::string file_report_name=id2string(file_it->first)+".deltacheck.html";
    std::ofstream file_report(file_report_name.c_str());
    
    if(!file_report)
    {
      error() << "failed to open report file `" << file_report
              << "'" << eom;
      return;
    }
    
    // read the goto-binary file
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

      file_report << "<h2>Function " << html_escape(symbol.display_name())
                  << " in " << html_escape(file_it->first)
                  << "</h2>\n";

      check_function(symbol, *index_fkt, ns, file_report);
    }
  }
  
  // Report grand totals
  
  global_report << "<h2>Summary Statistics</h2>\n";
  statistics.html_report_total(global_report);
}

/*******************************************************************\

Function: one_program_check

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void one_program_check(
  const indext &index,
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

  one_program_checkt opc(index, message_handler);
  
  opc.check_all(out);

  html_report_footer(out, index);
}  
