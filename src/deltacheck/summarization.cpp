/*******************************************************************\

Module: Summarization

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <fstream>

#include <config.h>
#include <xml.h>

#include <goto-programs/goto_inline.h>
#include <goto-programs/read_goto_binary.h>
#include <goto-programs/link_to_library.h>

#include "xml_conversion.h"
#include "summarization.h"
#include "transformer.h"

//#include "cgraph_builder.h"
//#include "modular_fptr_analysis.h"
//#include "modular_globals_analysis.h"

/*******************************************************************\

Function: summarize_function

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarize_function(
  const namespacet &ns, 
  const goto_functionst &goto_functions,
  const symbolt &symbol,
  const goto_functionst::goto_functiont &goto_function,
  std::ostream &out)
{
  out << "<function id=\"";
  xmlt::escape_attribute(id2string(symbol.name), out);
  out << "\">" << std::endl;
  
  if(symbol.location.is_not_nil() && symbol.location.get_file()!="")
    out << xml(symbol.location);

  transformer(ns, goto_functions, symbol, goto_function, out);

  out << "</function>" << std::endl;
  out << std::endl;
}

/*******************************************************************\

Function: dump_exported_functions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void dump_exported_functions(
  const namespacet &ns, 
  const goto_functionst &goto_functions,
  std::ostream &out)
{
  out << "<functions>" << std::endl;

  // do this for each function
  forall_goto_functions(f_it, goto_functions)
  {
    if(!f_it->second.body_available)
      continue;

    const symbolt &symbol=ns.lookup(f_it->first);
    
    if(symbol.file_local)
      continue;
  
    summarize_function(ns, goto_functions, symbol, f_it->second, out);
        
    out << "</function>" << std::endl;
  }
  
  out << "</functions>" << std::endl;
}

/*******************************************************************\

Function: dump_state_variables

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void dump_state_variables(
  const contextt &context,
  std::ostream &out)
{
  out << "<state_variables>" << std::endl;

  forall_symbols(s_it, context.symbols)
  {
    const symbolt &symbol=s_it->second;
  
    out << "<state_variable id=\"";
    xmlt::escape_attribute(id2string(symbol.name), out);
    out << "\">" << std::endl;
  
    if(symbol.location.is_not_nil() && symbol.location.get_file()!="")
      out << xml(symbol.location);

    out << "</state_variable>" << std::endl;
  }
  
  out << "</state_variables>" << std::endl;
}

/*******************************************************************\

Function: summarization

  Inputs:

 Outputs:

 Purpose: Phase I: produce a summary for a given file

\*******************************************************************/

void summarization(
  const contextt &context,
  const goto_functionst &goto_functions,
  const optionst &options,
  std::ostream &out)
{
  // first collect non-static function symbols that
  // have a body
  
  namespacet ns(context);
  
  dump_exported_functions(ns, goto_functions, out);
  
  dump_state_variables(context, out);
  
  #if 0
  cgraph_buildert cg_builder;
  modular_fptr_analysist fptr_analysis;
  modular_globals_analysist globals_analysis;
  
  cg_builder.add_analysis(&fptr_analysis);
  cg_builder.add_analysis(&globals_analysis);
  
  cg_builder.analyze_module(context, goto_functions);
  cg_builder.serialize(file_name);
  #endif
}

/*******************************************************************\

Function: summarization

  Inputs:

 Outputs:

 Purpose: Phase I: produce a summary for a given file

\*******************************************************************/

void summarization(
  const std::string &file_name,
  const optionst &options,
  message_handlert &message_handler)
{
  // get the goto program
  contextt context;
  goto_functionst goto_functions;

  if(read_goto_binary(
       file_name,
       context, goto_functions, message_handler))
    throw std::string("failed to read goto binary ")+file_name;
    
  config.ansi_c.set_from_context(context);

  // finally add the library
  link_to_library(
    context, goto_functions, options, message_handler);

  namespacet ns(context);

  // do partial inlining
  goto_partial_inline(goto_functions, ns, message_handler);
  
  // recalculate numbers, etc.
  goto_functions.update();

  // add loop ids
  goto_functions.compute_loop_numbers();
  
  std::string summary_file_name=file_name+".summary";
  std::ofstream summary_file(summary_file_name.c_str(),
    std::ios::binary|std::ios::trunc|std::ios::out);
  
  if(!summary_file)
    throw std::string("failed to write summary file");

  summary_file << "<summaries>" << std::endl;

  ::summarization(context, goto_functions, options, summary_file);

  summary_file << "</summaries>" << std::endl;
}

