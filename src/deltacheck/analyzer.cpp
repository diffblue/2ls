/*******************************************************************\

Module: Indexing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <fstream>

#include <util/message.h>
#include <util/time_stopping.h>
#include <util/memory_info.h>

//#include <solvers/sat/satcheck.h>
//#include <solvers/flattening/bv_pointers.h>

#include "../html/html_escape.h"
#include "../functions/path_util.h"

#include "html_report.h"
#include "ssa_fixed_point.h"
#include "statistics.h"
#include "report_source_code.h"
#include "analyzer.h"
#include "change_impact.h"

class deltacheck_analyzert:public messaget
{
public:
  deltacheck_analyzert(
    const std::string &_path_old,
    const goto_modelt &_goto_model_old,
    const std::string &_path_new,
    const goto_modelt &_goto_model_new,
    const optionst &_options,
    message_handlert &message_handler):
    messaget(message_handler),
    path_old(_path_old),
    path_new(_path_new),
    goto_model_old(_goto_model_old),
    goto_model_new(_goto_model_new),
    options(_options)
  {
  }
  
  statisticst statistics;
  
  void operator()();

protected:
  const std::string &path_old;
  const std::string &path_new;
  const goto_modelt &goto_model_old;
  const goto_modelt &goto_model_new;
  const optionst &options;
  
  change_impactt change_impact;
  
  void check_function(
    const irep_idt &,
    std::ostream &global_report);

  void check_all(std::ostream &global_report);
  
  unsigned errors_in_file, passed_in_file,
           unknown_in_file, unaffected_in_file,
           LOCs_in_file;
  
  void collect_statistics(const propertiest &);
  void collect_statistics(const goto_functionst::goto_functiont &);
};

/*******************************************************************\

Function: deltacheck_analyzert::check_function

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void deltacheck_analyzert::check_function(
  const irep_idt &function,
  std::ostream &global_report)
{
  const goto_functionst::function_mapt::const_iterator
    fmap_it_new=goto_model_new.goto_functions.function_map.find(function);
      
  if(fmap_it_new==goto_model_new.goto_functions.function_map.end())
  {
    error() << "failed to find function `" << function
            << "'" << eom;
    return;
  }
    
  const goto_functionst::goto_functiont &fkt_new=
    fmap_it_new->second;

  // update statistics
  LOCs_in_file+=fkt_new.body.instructions.size();
  collect_statistics(fkt_new);
  statistics.number_map["Functions"]++;      

  // Is this function at all affected?
  if(!change_impact.function_map[function].is_affected())
  {
    status() << "Function \"" << function << "\" is not affected" << eom;

    unsigned count=0;
    forall_goto_program_instructions(i_it, fkt_new.body)
      if(i_it->is_assert())
        count++;
    
    unaffected_in_file+=count;
    statistics.number_map["Unaffected"]+=count;
    return; // next function
  }
    
  status() << "Checking \"" << function << "\"" << eom;
  
  const namespacet ns_new(goto_model_new.symbol_table);
  const namespacet ns_old(goto_model_old.symbol_table);
    
  const symbolt &symbol_new=ns_new.lookup(function);
  
  // get corresponding goto_model_old function, if available

  const goto_functionst::function_mapt::const_iterator
    fmap_it_old=goto_model_old.goto_functions.function_map.find(function);
    
  goto_functionst::goto_functiont fkt_old_dummy;
  symbolt symbol_old_dummy;

  const goto_functionst::goto_functiont &fkt_old=
    fmap_it_old==goto_model_old.goto_functions.function_map.end()?fkt_old_dummy:
    fmap_it_old->second;
    
  const symbolt &symbol_old=
    fmap_it_old==goto_model_old.goto_functions.function_map.end()?symbol_old_dummy:
    ns_old.lookup(function);
    
  // set up report

  std::string report_file_name=
    make_relative_path(path_new, "deltacheck."+id2string(function)+".html");
    
  std::ofstream function_report(report_file_name.c_str());
  
  html_report_header("Function "+id2string(symbol_new.display_name()), function_report);

  // build SSA for each
  status() << "Building SSA" << eom;
  statistics.start("SSA");
  local_SSAt SSA_old(fkt_old, ns_old, "@old");
  local_SSAt SSA_new(fkt_new, ns_new);
  statistics.stop("SSA");

  // add assertions in old version as assumptions
  SSA_old.assertions_to_constraints();

  // now do _joint_ fixed-point
  namespacet joint_ns(
    ns_new.get_symbol_table(),
    ns_old.get_symbol_table());
  status() << "Joint data-flow fixed-point" << eom;
  statistics.start("Fixed-point");
  ssa_fixed_pointt ssa_fixed_point(SSA_old, SSA_new, joint_ns);
  statistics.stop("Fixed-point");
  
  // now report on assertions
  std::string description_old=
    options.get_option("description-old");

  std::string description_new=
    options.get_option("description-new");
    
  status() << "Reporting" << eom;
  statistics.start("Reporting");
  //report_properties(ssa_fixed_point.properties, function_report);  
  report_properties(ssa_fixed_point.properties, *this);  
  report_countermodels(SSA_old, SSA_new,
                       ssa_fixed_point.properties, function_report);
  report_source_code(
    path_old, symbol_old.location, fkt_old.body, description_old,
    path_new, symbol_new.location, fkt_new.body, description_new,
    ssa_fixed_point.properties,
    function_report, get_message_handler());
  statistics.stop("Reporting");
  
  // dump statistics
  statistics.html_report_last(function_report);

  // collect some more data
  #if 0
  collect_statistics(ssa_fixed_point.properties); 
  #endif

  function_report << "</body></html>\n";
  
  #if 0
  global_report << "<table class=\"file-table\">\n"
                << "<tr><th>File</th>"
                << "<th>LOCs</th>"
                << "<th># Errors</th>"
                << "</tr>\n";
  #endif
  
  #if 0    
    // add link to global report
    global_report << "<tr><td><a href=\"" << html_escape(report_url)
                  << "\">" << html_escape(file_it->first)
                  << "</a></td>"
                  << "<td align=\"right\">" << LOCs_in_file << "</td>"
                  << "<td align=\"right\">" << errors_in_file << "</td>"
                  << "</tr>\n";
  }
  
  global_report << "</table>\n\n";
  #endif
}

/*******************************************************************\

Function: deltacheck_analyzert::check_all

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void deltacheck_analyzert::check_all(std::ostream &global_report)
{
  // we do this by function in the new goto_model
  for(goto_functionst::function_mapt::const_iterator
      fmap_it=goto_model_new.goto_functions.function_map.begin();
      fmap_it!=goto_model_new.goto_functions.function_map.end();
      fmap_it++)
  {
    check_function(fmap_it->first, global_report);
  }
}

/*******************************************************************\

Function: deltacheck_analyzert::collect_statistics

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void deltacheck_analyzert::collect_statistics(
  const goto_functionst::goto_functiont &goto_function)
{
  statistics.number_map["LOCs"]+=goto_function.body.instructions.size();
}

/*******************************************************************\

Function: deltacheck_analyzert::collect_statistics

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void deltacheck_analyzert::collect_statistics(
  const propertiest &properties)
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

Function: deltacheck_analyzert::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void deltacheck_analyzert::operator()()
{
  statistics.start("Total-time");

  std::string report_file_name=
    make_relative_path(path_new, "deltacheck.html");
    
  std::ofstream out(report_file_name.c_str());
  
  if(!out)
  {
    error() << "failed to write to \""
            << report_file_name << "\"" << eom;
    return;
  }
  
  status() << "Writing report into \""
           << report_file_name << "\"" << eom;
           
  std::string title="DeltaCheck Summary";

  html_report_header(
    out, options.get_option("description-old"),
         options.get_option("description-new"), title);

  statistics.start("Change-impact");
  status() << "Computing syntactic difference" << eom;
  change_impact.diff(goto_model_old, goto_model_new);
  status() << "Change-impact analysis" << eom;
  change_impact.change_impact(goto_model_new);
  statistics.stop("Change-impact");

  status() << "Starting analysis" << eom;

  if(options.get_option("function")!="")
    check_function(options.get_option("function"), out);
  else
    check_all(out);

  statistics.stop("Total-time");
    
  // Report grand totals
  
  out << "<h2>Summary statistics</h2>\n";
  statistics.html_report_total(out);
  
  result() << "Properties unaffected: " << statistics.number_map["Unaffected"] << eom;
  result() << "Properties passed: " << statistics.number_map["Passed"] << eom;
  result() << "Properties failed: " << statistics.number_map["Errors"] << eom;
  result() << "Properties warned: " << statistics.number_map["Unknown"] << eom;

  messaget::statistics() << "LOCs analyzed: " << statistics.number_map["LOCs"] << eom;
  messaget::statistics() << "Functions analyzed: " << statistics.number_map["Functions"] << eom;
  
  memory_info(messaget::statistics());
  messaget::statistics() << eom;

  html_report_footer(out);
  
  // Write some statistics into a JSON file, for the benefit
  // of other programs.
  
  std::string stat_file_name=
    make_relative_path(path_new, "deltacheck-stat.json");
  std::ofstream json_out(stat_file_name.c_str());
  
  json_out << "{\n";
  json_out << "  \"properties\": {\n";
  json_out << "    \"unaffected\": " << statistics.number_map["Unaffected"] << ",\n";
  json_out << "    \"passed\": " << statistics.number_map["Passed"] << ",\n";
  json_out << "    \"failed\": " << statistics.number_map["Errors"] << ",\n";
  json_out << "    \"warned\": " << statistics.number_map["Unknown"] << "\n";
  json_out << "  },\n";
  json_out << "  \"program\": {\n";
  json_out << "    \"LOCs\": " << statistics.number_map["LOCs"] << ",\n";
  json_out << "    \"functions\": " << statistics.number_map["Functions"] << "\n";
  json_out << "  }\n";
  json_out << "}\n";
}  

/*******************************************************************\

Function: deltacheck_analyzer

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void deltacheck_analyzer(
  const std::string &path1,
  const goto_modelt &goto_model1,
  const std::string &path2,
  const goto_modelt &goto_model2,
  const optionst &options,
  message_handlert &message_handler)
{
  deltacheck_analyzert checker(
    path1, goto_model1,
    path2, goto_model2,
    options, message_handler);
  checker();
}
