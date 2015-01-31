/*******************************************************************\

Module: Indexing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <fstream>

#include <util/message.h>
#include <util/time_stopping.h>
#include <util/memory_info.h>

#include <goto-programs/read_goto_binary.h>
#include <goto-programs/goto_model.h>
#include <goto-programs/goto_inline.h>
#include <goto-programs/set_properties.h>

#include <goto-symex/goto_symex.h>
#include <goto-symex/symex_target_equation.h>

#include <analyses/goto_check.h>

#include <solvers/sat/satcheck.h>
#include <solvers/flattening/bv_pointers.h>

#include "../html/html_escape.h"
#include "../functions/index.h"
#include "../functions/get_function.h"
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
    const indext &_index,
    const optionst &_options,
    message_handlert &message_handler):
    messaget(message_handler),
    use_index_old(false),
    index_old(dummy_index_old), index_new(_index), options(_options)
  {
  }
  
  deltacheck_analyzert(
    const indext &_index_old,
    const indext &_index_new,
    const optionst &_options,
    message_handlert &message_handler):
    messaget(message_handler),
    use_index_old(true),
    index_old(_index_old), index_new(_index_new), options(_options)
  {
  }
  
  statisticst statistics;
  
  void operator()();

protected:
  bool use_index_old;
  indext dummy_index_old;
  const indext &index_old;
  const indext &index_new;
  const optionst &options;
  
  change_impactt change_impact;
  
  void check_function(
    const std::string &path_prefix,
    const symbolt &symbol,
    goto_functionst::goto_functiont &f,
    const namespacet &ns,
    std::ostream &file_report);

  void check_function_delta(
    // old
    const std::string &path_prefix_old,
    const symbolt &symbol_old,
    goto_functionst::goto_functiont &f_old,
    const namespacet &ns_old,
    // new
    const std::string &path_prefix_new,
    const symbolt &symbol,
    goto_functionst::goto_functiont &f,
    const namespacet &ns,
    // output
    std::ostream &file_report);

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
  const std::string &path_prefix,
  const symbolt &symbol,
  goto_functionst::goto_functiont &f,
  const namespacet &ns,
  std::ostream &file_report)
{
  // add properties
  status() << "Generating properties" << eom;
  statistics.start("Properties");
  goto_check(ns, options, f);
  f.body.update();
  label_properties(f.body);
  statistics.stop("Properties");

  // build SSA
  status() << "Building SSA" << eom;
  statistics.start("SSA");
  local_SSAt SSA(f, ns);
  statistics.stop("SSA");
  
  // now do fixed-point
  status() << "Data-flow fixed-point" << eom;
  statistics.start("Fixed-point");
  ssa_fixed_pointt ssa_fixed_point(SSA, ns);
  statistics.stop("Fixed-point");
  
  // now report on assertions
  status() << "Reporting" << eom;
  statistics.start("Reporting");
  report_properties(ssa_fixed_point.properties, file_report);  
  report_properties(ssa_fixed_point.properties, *this);  
  report_countermodels(SSA, ssa_fixed_point.properties, file_report);  
  report_source_code(
    path_prefix, symbol.location, f.body,
    ssa_fixed_point.properties, file_report,
    get_message_handler());
  file_report << "\n";
  statistics.stop("Reporting");
  
  // dump statistics
  statistics.html_report_last(file_report);
  
  // collect some more data
  collect_statistics(ssa_fixed_point.properties); 
}

/*******************************************************************\

Function: deltacheck_analyzert::check_function_delta

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void deltacheck_analyzert::check_function_delta(
  // old
  const std::string &path_prefix_old,
  const symbolt &symbol_old,
  goto_functionst::goto_functiont &f_old,
  const namespacet &ns_old,
  // new
  const std::string &path_prefix_new,
  const symbolt &symbol_new,
  goto_functionst::goto_functiont &f_new,
  const namespacet &ns_new,
  std::ostream &file_report)
{
  // add properties to each
  status() << "Generating properties" << eom;
  statistics.start("Properties");
  goto_check(ns_old, options, f_old);
  f_old.body.update();
  label_properties(f_old.body);
  goto_check(ns_new, options, f_new);
  f_new.body.update();
  label_properties(f_new.body);
  statistics.stop("Properties");

  // build SSA for each
  status() << "Building SSA" << eom;
  statistics.start("SSA");
  local_SSAt SSA_old(f_old, ns_old, "@old");
  local_SSAt SSA_new(f_new, ns_new);
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
    index_old.description==""?"old version":index_old.description;

  std::string description_new=
    index_new.description==""?"new version":index_new.description;
  
  status() << "Reporting" << eom;
  statistics.start("Reporting");
  report_properties(ssa_fixed_point.properties, file_report);  
  report_properties(ssa_fixed_point.properties, *this);  
  report_countermodels(SSA_old, SSA_new,
                       ssa_fixed_point.properties, file_report);  
  report_source_code(
    path_prefix_old, symbol_old.location, f_old.body, description_old,
    path_prefix_new, symbol_new.location, f_new.body, description_new,
    ssa_fixed_point.properties,
    file_report, get_message_handler());
  file_report << "\n";
  statistics.stop("Reporting");
  
  // dump statistics
  statistics.html_report_last(file_report);

  // collect some more data
  collect_statistics(ssa_fixed_point.properties); 
}

/*******************************************************************\

Function: deltacheck_analyzert::check_all

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool loops(const goto_programt &src)
{
  forall_goto_program_instructions(it, src)
    if(it->is_backwards_goto()) return true;
  return false;
}

void deltacheck_analyzert::check_all(std::ostream &global_report)
{
  // we do this by file in the index
  
  status() << "Starting analysis" << eom;

  get_functiont get_old_function(index_old);
  get_old_function.set_message_handler(get_message_handler());
  
  global_report << "<table class=\"file-table\">\n"
                << "<tr><th>File</th>"
                << "<th>LOCs</th>"
                << "<th># Errors</th>"
                << "</tr>\n";
  
  for(indext::file_to_functiont::const_iterator
      file_it=index_new.file_to_function.begin();
      file_it!=index_new.file_to_function.end();
      file_it++)
  {
    std::string full_path=index_new.full_path(file_it->first);      
    std::string path_prefix=get_directory(full_path);
  
    status() << "Processing \"" << full_path << "\"" << eom;
    
    errors_in_file=unknown_in_file=passed_in_file=unaffected_in_file=0;
    LOCs_in_file=0;
    
    std::string file_suffix=
      use_index_old?".deltacheck-diff.html":".deltacheck.html";
    
    std::string file_report_name=full_path+file_suffix;
    std::string report_url=id2string(file_it->first)+file_suffix;
    
    std::ofstream file_report(file_report_name.c_str());
    
    if(!file_report)
    {
      error() << "failed to open report file `" << file_report
              << "'" << eom;
      return;
    }
    
    std::string title="DeltaCheck File";

    if(use_index_old)
      html_report_header(file_report, index_old, index_new, title);
    else    
      html_report_header(file_report, index_new, title);
    
    // read the goto-binary file
    goto_modelt model;
    read_goto_binary(full_path, model, get_message_handler());
    
    // do partial inlining to increase precision
    if(options.get_bool_option("partial-inlining"))
    {
      #if 0
      status() << "Partial inlining" << eom;
      goto_partial_inline(model, get_message_handler(), 30);
      #endif
    }
   
    const namespacet ns_new(model.symbol_table); 
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
      
      goto_functionst::goto_functiont *index_new_fkt=
        &fmap_it->second;

      // update statistics
      LOCs_in_file+=index_new_fkt->body.instructions.size();
      collect_statistics(*index_new_fkt);
      statistics.number_map["Functions"]++;      
    
      // In case of differential checking, is this function at all affected?
      if(use_index_old)
        if(!change_impact.file_map[file_it->first][id].is_affected())
        {
          status() << "Function \"" << id2string(id) << "\" is not affected" << eom;

          // add properties to function
          statistics.start("Properties");
          goto_check(ns_new, options, *index_new_fkt);
          index_new_fkt->body.update();
          statistics.stop("Properties");

          unsigned count=0;
          forall_goto_program_instructions(i_it, index_new_fkt->body)
            if(i_it->is_assert())
              count++;
          
          unaffected_in_file+=count;
          statistics.number_map["Unaffected"]+=count;
          continue; // next function
        }
      
      status() << "Checking \"" << id2string(id) << "\"" << eom;
      
      const symbolt &symbol=ns_new.lookup(id);

      file_report << "<h2>Function " << html_escape(symbol.display_name())
                  << " in " << html_escape(file_it->first)
                  << "</h2>\n";

      // get corresponding index_old function, if available
      
      std::string path_prefix_old;
    
      goto_functionst::goto_functiont *index_old_fkt=
        get_old_function(id);
    
      if(index_old_fkt!=NULL)
      {
        const namespacet &ns_old=get_old_function.ns;
        const symbolt &symbol_old=ns_old.lookup(id);
        std::string path_prefix_old=
          get_directory(id2string(get_old_function.get_file_name()));

        check_function_delta(
          path_prefix_old, symbol_old, *index_old_fkt, ns_old,
          path_prefix,     symbol,     *index_new_fkt, ns_new,
          file_report);
      }
      else
      {
        #if 1
        check_function(path_prefix, symbol, *index_new_fkt, ns_new,
                       file_report);
        #else
        if(symbol.name==ID_main)
        {
        }
        else if(loops(index_new_fkt->body) || symbol.name!="main")
          check_function(path_prefix, symbol, *index_new_fkt, ns_new,
                         file_report);
        else
        {
          goto_check(ns_new, options, *index_new_fkt);
          index_new_fkt->body.update();

          symbol_tablet d;
          namespacet joint(d, model.symbol_table);
          symex_target_equationt e(joint);
          goto_symext symex(joint, d, e);
        
          symex(model.goto_functions, index_new_fkt->body);

          satcheckt satcheck;
          satcheck.set_message_handler(get_message_handler());
          bv_pointerst solver(joint, satcheck);
          solver.set_message_handler(get_message_handler());
          e.convert(solver);
          decision_proceduret::resultt r=solver.dec_solve();

          for(symex_target_equationt::SSA_stepst::iterator
              it=e.SSA_steps.begin();
              it!=e.SSA_steps.end();
              it++)
          {
            if(it->is_assert())
            {
              tvt result;
              if(r==decision_proceduret::D_SATISFIABLE)
                result=solver.prop.l_get(it->cond_literal);
              else
                result=tvt(true);

              if(result.is_false())
                statistics.number_map["Errors"]++;
              else
                statistics.number_map["Passed"]++;
            }
          }
        }
        #endif
      }
    }

    html_report_footer(file_report);
    
    // add link to global report
    global_report << "<tr><td><a href=\"" << html_escape(report_url)
                  << "\">" << html_escape(file_it->first)
                  << "</a></td>"
                  << "<td align=\"right\">" << LOCs_in_file << "</td>"
                  << "<td align=\"right\">" << errors_in_file << "</td>"
                  << "</tr>\n";
  }
  
  global_report << "</table>\n\n";
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

void deltacheck_analyzert::collect_statistics(const propertiest &properties)
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
    use_index_old?"deltacheck-diff.html":"deltacheck.html";
    
  std::string report_full_path=
    make_relative_path(index_new.path_prefix, report_file_name);

  std::ofstream out(report_full_path.c_str());
  
  if(!out)
  {
    error() << "failed to write to \""
            << report_full_path << "\"" << eom;
    return;
  }
  
  status() << "Writing report into \""
           << report_full_path << "\"" << eom;
           
  std::string title="DeltaCheck Summary";

  if(use_index_old)
    html_report_header(out, index_old, index_new, title);
  else
    html_report_header(out, index_new, title);

  if(use_index_old)
  {
    status() << "Path prefix old: " << index_old.path_prefix << eom;
    status() << "Path prefix new: " << index_new.path_prefix << eom;
  }
  else
    status() << "Path prefix: " << index_new.path_prefix << eom;
    
  if(use_index_old)
  {
    statistics.start("Change-impact");
    status() << "Computing syntactic difference" << eom;
    change_impact.diff(index_old, index_new);
    status() << "Change-impact analysis" << eom;
    change_impact.change_impact(index_new);
    statistics.stop("Change-impact");
  }

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
  
  // Write some statistics into an XML file, for the benefit
  // of other programs.
  
  std::string stat_xml_full_path=
    make_relative_path(index_new.path_prefix, "deltacheck-stat.xml");

  std::ofstream xml_out(stat_xml_full_path.c_str());
  
  xml_out << "<deltacheck_stat>\n";
  xml_out << "<properties";
  xml_out << " unaffected=\"" << statistics.number_map["Unaffected"] << "\"";
  xml_out << " passed=\"" << statistics.number_map["Passed"] << "\"";
  xml_out << " failed=\"" << statistics.number_map["Errors"] << "\"";
  xml_out << " warned=\"" << statistics.number_map["Unknown"] << "\"";
  xml_out << ">\n";
  xml_out << "</properties>\n";
  xml_out << "<program";
  xml_out << " LOCs=\"" << statistics.number_map["LOCs"] << "\"";
  xml_out << " Functions=\"" << statistics.number_map["Functions"] << "\"";
  xml_out << ">\n";
  xml_out << "</program>\n";
  xml_out << "</deltacheck_stat>\n";
}  

/*******************************************************************\

Function: one_program_analyzer

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void one_program_analyzer(
  const indext &index,
  const optionst &options,
  message_handlert &message_handler)
{
  deltacheck_analyzert checker(index, options, message_handler);
  checker();
}  

/*******************************************************************\

Function: deltacheck_analyzer

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void deltacheck_analyzer(
  const indext &index1,
  const indext &index2,
  const optionst &options,
  message_handlert &message_handler)
{
  deltacheck_analyzert checker(index1, index2, options, message_handler);
  checker();
}
