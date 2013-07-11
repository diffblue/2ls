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

#include "checker.h"
#include "index.h"
#include "html_report.h"
#include "get_function.h"
#include "ssa_data_flow.h"
#include "html_escape.h"
#include "statistics.h"
#include "extract_source.h"

class deltacheck_checkert:public messaget
{
public:
  deltacheck_checkert(
    const indext &_index,
    const optionst &_options,
    message_handlert &message_handler):
    messaget(message_handler),
    use_index_old(false),
    index_old(dummy_index_old), index(_index), options(_options)
  {
  }
  
  deltacheck_checkert(
    const indext &_index_old,
    const indext &_index,
    const optionst &_options,
    message_handlert &message_handler):
    messaget(message_handler),
    use_index_old(true),
    index_old(_index_old), index(_index), options(_options)
  {
  }
  
  statisticst statistics;
  
  void operator()();

protected:
  bool use_index_old;
  indext dummy_index_old;
  const indext &index_old;
  const indext &index;
  const optionst &options;
  
  void check_function(
    const symbolt &symbol,
    goto_functionst::goto_functiont &f,
    const namespacet &ns,
    std::ostream &file_report);

  void check_function(
    // old
    const symbolt &symbol_old,
    goto_functionst::goto_functiont &f_old,
    const namespacet &ns_old,
    // new
    const symbolt &symbol,
    goto_functionst::goto_functiont &f,
    const namespacet &ns,
    // output
    std::ostream &file_report);

  void check_all(std::ostream &global_report);
  
  unsigned errors_in_file, passed_in_file, unknown_in_file;
  
  void collect_statistics(const propertiest &properties);
};

/*******************************************************************\

Function: deltacheck_checkert::check_function

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void deltacheck_checkert::check_function(
  const symbolt &symbol,
  goto_functionst::goto_functiont &f,
  const namespacet &ns,
  std::ostream &file_report)
{
  statistics.number_map["Functions"]++;
  statistics.number_map["LOCs"]+=f.body.instructions.size();

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
  html_report(ssa_data_flow.properties, file_report);  
  extract_source(
    index.path_prefix, symbol.location, f.body,
    ssa_data_flow.properties, file_report,
    get_message_handler());
  file_report << "\n";
  statistics.stop("Reporting");
  
  // dump statistics
  statistics.html_report_last(file_report);
  
  // collect some more data
  collect_statistics(ssa_data_flow.properties); 
}

/*******************************************************************\

Function: deltacheck_checkert::check_function

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void deltacheck_checkert::check_function(
  const symbolt &symbol_old,
  goto_functionst::goto_functiont &f_old,
  const namespacet &ns_old,
  const symbolt &symbol,
  goto_functionst::goto_functiont &f,
  const namespacet &ns,
  std::ostream &file_report)
{
  statistics.number_map["Functions"]++;
  statistics.number_map["LOCs"]+=f.body.instructions.size();

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
  html_report(ssa_data_flow.properties, file_report);  
  extract_source(index_old.path_prefix, symbol_old.location, f_old.body,
                 index.path_prefix, symbol.location, f.body, ssa_data_flow.properties,
                 file_report, get_message_handler());
  file_report << "\n";
  statistics.stop("Reporting");
  
  // dump statistics
  statistics.html_report_last(file_report);

  // collect some more data
  collect_statistics(ssa_data_flow.properties); 
}

/*******************************************************************\

Function: deltacheck_checkert::check_all

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void deltacheck_checkert::check_all(std::ostream &global_report)
{
  // we do this by file in the index

  get_functiont get_old_function(index_old);
  get_old_function.set_message_handler(get_message_handler());
  
  global_report << "<table class=\"file-table\">\n"
                << "<tr><th>File</th><th># Errors</th></tr>\n";
  
  for(indext::file_to_functiont::const_iterator
      file_it=index.file_to_function.begin();
      file_it!=index.file_to_function.end();
      file_it++)
  {
    status() << "Processing \"" << file_it->first << "\"" << eom;
    
    errors_in_file=unknown_in_file=passed_in_file=0;
    
    std::string file_report_name=id2string(file_it->first)+".deltacheck.html";
    std::ofstream file_report(file_report_name.c_str());
    
    if(!file_report)
    {
      error() << "failed to open report file `" << file_report
              << "'" << eom;
      return;
    }

    if(use_index_old)
      html_report_header(file_report, index_old, index);
    else    
      html_report_header(file_report, index);
    
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

      // get corresponding index_old function, if available
    
      goto_functionst::goto_functiont *index_old_fkt=
        get_old_function(id);
    
      if(index_old_fkt!=NULL)
      {
        const namespacet &ns_old=get_old_function.ns;
        const symbolt &symbol_old=ns_old.lookup(id);

        check_function(symbol_old, *index_old_fkt, ns_old,
                       symbol, *index_fkt, ns,
                       file_report);
      }
      else
        check_function(symbol, *index_fkt, ns, file_report);
    }

    html_report_footer(file_report);
    
    // add link to global report
    global_report << "<tr><td><a href=\"" << file_report_name
                  << "\">" << html_escape(file_it->first)
                  << "</a></td>"
                  << "<td align=\"right\">" << errors_in_file << "</td>"
                  << "</tr>\n";
  }
  
  global_report << "</table>\n\n";
  
  // Report grand totals
  
  global_report << "<h2>Summary statistics</h2>\n";
  statistics.html_report_total(global_report);
  
  result() << "Properties passed: " << statistics.number_map["Passed"] << eom;
  result() << "Properties failed: " << statistics.number_map["Errors"] << eom;
}

/*******************************************************************\

Function: deltacheck_checkert::collect_statistics

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void deltacheck_checkert::collect_statistics(const propertiest &properties)
{
  for(propertiest::const_iterator
      p_it=properties.begin();
      p_it!=properties.end();
      p_it++)
  {
    if(p_it->status.is_false())
    {
      errors_in_file++;
      statistics.number_map["Errors"]++;
    }
    else if(p_it->status.is_true())
    {
      passed_in_file++;
      statistics.number_map["Passed"]++;
    }
    else
    {
      unknown_in_file++;
      statistics.number_map["Unknown"]++;
    }
  }
}

/*******************************************************************\

Function: deltacheck_checkert::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void deltacheck_checkert::operator()()
{
  std::string report_file_name="deltacheck.html";
  std::ofstream out(report_file_name.c_str());
  
  if(!out)
  {
    error() << "failed to write to \""
            << report_file_name << "\"" << eom;
    return;
  }
  
  status() << "Writing report into \""
           << report_file_name << "\"" << eom;

  if(use_index_old)
    html_report_header(out, index_old, index);
  else
    html_report_header(out, index);

  check_all(out);

  html_report_footer(out);
}  

/*******************************************************************\

Function: one_program_check

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void one_program_check(
  const indext &index,
  const optionst &options,
  message_handlert &message_handler)
{
  deltacheck_checkert checker(index, options, message_handler);
  checker();
}  

/*******************************************************************\

Function: delta_check

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void delta_check(
  const indext &index1,
  const indext &index2,
  const optionst &options,
  message_handlert &message_handler)
{
  deltacheck_checkert checker(index1, index2, options, message_handler);
  checker();
}
