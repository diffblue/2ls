/*******************************************************************\

Module: Summarizer Command Line Options Processing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cstdlib>
#include <iostream>
#include <fstream>

#include <util/string2int.h>
#include <util/config.h>
#include <util/language.h>
#include <util/options.h>
#include <util/memory_info.h>

#include <ansi-c/ansi_c_language.h>
#include <cpp/cpp_language.h>

#include <goto-programs/goto_convert_functions.h>
#include <goto-programs/show_properties.h>
#include <goto-programs/set_properties.h>
#include <goto-programs/remove_function_pointers.h>
#include <goto-programs/read_goto_binary.h>
#include <goto-programs/loop_ids.h>
#include <goto-programs/link_to_library.h>
#include <goto-programs/goto_inline.h>
#include <goto-programs/goto_functions.h>
#include <goto-programs/xml_goto_trace.h>
#include <goto-programs/remove_returns.h>

#include <analyses/goto_check.h>

#include <langapi/mode.h>

#include <cbmc/version.h>

#include "summarizer_parseoptions.h"
#include "summary_db.h"
#include "summarizer.h"
#include "summary_checker.h"
#include "show.h"

/*******************************************************************\

Function: summarizer_parseoptionst::summarizer_parseoptionst

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

summarizer_parseoptionst::summarizer_parseoptionst(int argc, const char **argv):
  parseoptions_baset(SUMMARIZER_OPTIONS, argc, argv),
  language_uit("Summarizer " CBMC_VERSION, cmdline)
{
}
  
/*******************************************************************\

Function: summarizer_parseoptionst::eval_verbosity

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarizer_parseoptionst::eval_verbosity()
{
  // this is our default verbosity
  int v=messaget::M_STATISTICS;
  
  if(cmdline.isset("verbosity"))
  {
    v=unsafe_string2int(cmdline.getval("verbosity"));
    if(v<0)
      v=0;
    else if(v>10)
      v=10;
  }
  
  ui_message_handler.set_verbosity(v);
}

/*******************************************************************\

Function: summarizer_parseoptionst::get_command_line_options

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarizer_parseoptionst::get_command_line_options(optionst &options)
{
  if(config.set(cmdline))
  {
    usage_error();
    exit(1);
  }

  if(cmdline.isset("debug-level"))
    options.set_option("debug-level", cmdline.getval("debug-level"));

  if(cmdline.isset("unwindset"))
    options.set_option("unwindset", cmdline.getval("unwindset"));

  if(cmdline.isset("unwind"))
    options.set_option("unwind", cmdline.getval("unwind"));

  // check array bounds
  if(cmdline.isset("bounds-check"))
    options.set_option("bounds-check", true);
  else
    options.set_option("bounds-check", false);

  // check division by zero
  if(cmdline.isset("div-by-zero-check"))
    options.set_option("div-by-zero-check", true);
  else
    options.set_option("div-by-zero-check", false);

  // check overflow/underflow
  if(cmdline.isset("signed-overflow-check"))
    options.set_option("signed-overflow-check", true);
  else
    options.set_option("signed-overflow-check", false);

  // check overflow/underflow
  if(cmdline.isset("unsigned-overflow-check"))
    options.set_option("unsigned-overflow-check", true);
  else
    options.set_option("unsigned-overflow-check", false);

  // check overflow on floats
  if(cmdline.isset("float-overflow-check"))
    options.set_option("float-overflow-check", true);
  else
    options.set_option("float-overflow-check", false);

  // check for NaN (not a number)
  if(cmdline.isset("nan-check"))
    options.set_option("nan-check", true);
  else
    options.set_option("nan-check", false);

  // check pointers
  if(cmdline.isset("pointer-check"))
    options.set_option("pointer-check", true);
  else
    options.set_option("pointer-check", false);

  // check for memory leaks
  if(cmdline.isset("memory-leak-check"))
    options.set_option("memory-leak-check", true);
  else
    options.set_option("memory-leak-check", false);

  // check assertions
  if(cmdline.isset("no-assertions"))
    options.set_option("assertions", false);
  else
    options.set_option("assertions", true);

  // use assumptions
  if(cmdline.isset("no-assumptions"))
    options.set_option("assumptions", false);
  else
    options.set_option("assumptions", true);

  // magic error label
  if(cmdline.isset("error-label"))
    options.set_option("error-label", cmdline.getval("error-label"));
}

/*******************************************************************\

Function: summarizer_parseoptionst::doit

  Inputs:

 Outputs:

 Purpose: invoke main modules

\*******************************************************************/

int summarizer_parseoptionst::doit()
{
  if(cmdline.isset("version"))
  {
    std::cout << CBMC_VERSION << std::endl;
    return 0;
  }

  //
  // command line options
  //

  optionst options;
  get_command_line_options(options);

  eval_verbosity();
  
  //
  // Print a banner
  //
  status("SUMMARIZER version tbd");

  register_language(new_ansi_c_language);
  register_language(new_cpp_language);

  goto_modelt goto_model;

  if(get_goto_program(options, goto_model))
    return 6;

  // options for various debug outputs
    
  if(cmdline.isset("show-ssa"))
  {
    bool simplify=!cmdline.isset("no-simplify");
    show_ssa(goto_model, simplify, std::cout, ui_message_handler);
    return 7;
  }

  if(cmdline.isset("show-fixed-points"))
  {
    bool simplify=!cmdline.isset("no-simplify");
    show_fixed_points(goto_model, simplify, std::cout, ui_message_handler);
    return 7;
  }

  if(cmdline.isset("show-stats"))
  {
    show_stats(goto_model, std::cout);
    return 7;
  }

  if(cmdline.isset("show-defs"))
  {
    show_defs(goto_model, std::cout, ui_message_handler);
    return 7;
  }

  if(cmdline.isset("show-assignments"))
  {
    show_assignments(goto_model, std::cout, ui_message_handler);
    return 7;
  }

  if(cmdline.isset("show-guards"))
  {
    show_guards(goto_model, std::cout, ui_message_handler);
    return 7;
  }

  if(cmdline.isset("context-sensitive"))
  {
    options.set_option("context-sensitive", true);
    status() << "Context-sensitive analysis from " << 
      goto_model.goto_functions.entry_point() << eom;
  }

  if(cmdline.isset("arrays"))
  {
    options.set_option("arrays", true);
    status() << "Do not ignore array contents" << eom;
  }

  if(cmdline.isset("havoc"))
  {
    options.set_option("havoc", true);
    status() << "Havocking loops and function calls";
  }
  else if(cmdline.isset("equalities"))
  {
    options.set_option("equalities", true);
    status() << "Using equalities domain ";
  }
  else 
  {
    if(cmdline.isset("zones"))
      {
	options.set_option("zones", true);
	status() << "Using zones domain ";
      }
    else if(cmdline.isset("octagons"))
      {
	options.set_option("octagons", true);
	status() << "Using octagons domain ";
      }
    else //if(cmdline.isset("intervals")) //default
      {
	options.set_option("intervals", true);
	status() << "Using intervals domain ";
      }

    if(cmdline.isset("enum-solver")) 
      {
	options.set_option("enum-solver", true);
	status() << "with enumeration solver";
      }
    else //if(cmdline.isset("binsearch-solver")) //default
      {
	options.set_option("binsearch-solver", true);
	status() << "with binary search solver";
      }
  }
  status() << eom;

  if((cmdline.isset("equalities") || cmdline.isset("havoc")) &&
     cmdline.isset("enum-solver"))
  {
    warning() << "Option --enum-solver ignored" << eom;
  }
  if((cmdline.isset("equalities") || cmdline.isset("havoc"))  &&
     cmdline.isset("binsearch-solver"))
  {
    warning() << "Option --binsearch-solver ignored" << eom;
  }
  if(cmdline.isset("havoc")  &&
    cmdline.isset("equalities"))
  {
    warning() << "Option --equalities ignored" << eom;
  }
  if((cmdline.isset("equalities") || cmdline.isset("havoc"))  &&
     cmdline.isset("intervals"))
  {
    warning() << "Option --intervals ignored" << eom;
  }
  if((cmdline.isset("equalities") || cmdline.isset("havoc"))  &&
     cmdline.isset("zones"))
  {
    warning() << "Option --zones ignored" << eom;
  }
  if((cmdline.isset("equalities") || cmdline.isset("havoc"))  &&
     cmdline.isset("octagons"))
  {
    warning() << "Option --octagons ignored" << eom;
  }

  try
  {
    summary_checkert summary_checker(options);
    
    summary_checker.set_message_handler(get_message_handler());
    summary_checker.simplify=!cmdline.isset("no-simplify");
    summary_checker.fixed_point=!cmdline.isset("no-fixed-point");

    if(cmdline.isset("show-vcc"))
    {
      std::cout << "VERIFICATION CONDITIONS:\n\n";
      summary_checker.show_vcc=true;
      summary_checker(goto_model);
      return 0;
    }
    
    // do actual analysis
    switch(summary_checker(goto_model))
    {
    case property_checkert::PASS:
      report_properties(goto_model, summary_checker.property_map);
      report_success();
      return 0;
    
    case property_checkert::FAIL:
      report_properties(goto_model, summary_checker.property_map);
      report_failure();
      return 10;
    
    default:
      return 8;
    }
  }
  
  catch(const std::string error_msg)
  {
    error() << error_msg << messaget::eom;
    return 8;
  }

  catch(const char *error_msg)
  {
    error() << error_msg << messaget::eom;
    return 8;
  }

  #if 0                                         
  // let's log some more statistics
  debug() << "Memory consumption:" << messaget::endl;
  memory_info(debug());
  debug() << eom;
  #endif
}


/*******************************************************************\

Function: summarizer_parseoptionst::show_stats

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/


void summarizer_parseoptionst::expr_stats_rec(
    const exprt &expr,
    expr_statst &stats)
{
  
  if(expr.id()==ID_sideeffect)
  {
    const side_effect_exprt &side_effect_expr=to_side_effect_expr(expr);
    const irep_idt &statement=side_effect_expr.get_statement();

    if(statement==ID_malloc)
    {
      stats.has_malloc=true;
    }
    else if(statement==ID_nondet)
    {
      // done in statet:instantiate_rec
    }
  }

  if(expr.id()==ID_symbol )
  {
  
  }
  
  if(expr.has_operands())
  {
    forall_operands(it, expr)
    {
      expr_stats_rec(*it, stats);    
    }
  }
}
      

/*******************************************************************\

Function: summarizer_parseoptionst::expr_stats_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarizer_parseoptionst::show_stats(const goto_modelt &goto_model,
                                          std::ostream &out)
{

  expr_statst stats;

  unsigned nr_functions=0;

  // analyze all the functions
  forall_goto_functions(f_it, goto_model.goto_functions)
  {
    if(!f_it->second.body_available) continue;

    ++nr_functions;

    const goto_programt &goto_program=f_it->second.body;

    for(goto_programt::instructionst::const_iterator
      i_it=goto_program.instructions.begin();
      i_it!=goto_program.instructions.end();
      i_it++)
    {
      const goto_programt::instructiont &instruction=*i_it;

      switch(instruction.type)
      {
        case ASSIGN:
          {
            const code_assignt &assign=to_code_assign(instruction.code);
            expr_stats_rec(assign.lhs(), stats);          
            expr_stats_rec(assign.rhs(), stats);          
          }
          break;
        case ASSUME:
          expr_stats_rec(instruction.guard, stats);
          break;
        case ASSERT:
          expr_stats_rec(instruction.guard, stats);
          break;
        case GOTO:
          expr_stats_rec(instruction.guard, stats);
          break;
        default:
          // skip
          break;
      } // switch
    } // forall instructions
  } // forall functions

  out << " =============== STATS  =============== " << std::endl;
  out << "  nr of functions " << nr_functions << std::endl; 
  out << "  malloc " << (stats.has_malloc ? "YES" : "NO") << std::endl;
  out << "  arrays " << (stats.has_malloc ? "YES" : "NO") << std::endl;
  out << "  strings " << (stats.has_malloc ? "YES" : "NO") << std::endl;
}


/*******************************************************************\

Function: summarizer_parseoptionst::set_properties

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool summarizer_parseoptionst::set_properties(goto_modelt &goto_model)
{
  try
  {
    if(cmdline.isset("property"))
      ::set_properties(goto_model, cmdline.get_values("property"));
  }

  catch(const char *e)
  {
    error(e);
    return true;
  }

  catch(const std::string e)
  {
    error(e);
    return true;
  }
  
  catch(int)
  {
    return true;
  }
  
  return false;
}

/*******************************************************************\

Function: summarizer_parseoptionst::get_goto_program

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
  
bool summarizer_parseoptionst::get_goto_program(
  const optionst &options,
  goto_modelt &goto_model)
{
  if(cmdline.args.size()==0)
  {
    error() << "Please provide a program to verify" << eom;
    return true;
  }

  try
  {
    if(cmdline.args.size()==1 &&
       is_goto_binary(cmdline.args[0]))
    {
      status() << "Reading GOTO program from file" << eom;

      if(read_goto_binary(cmdline.args[0],
           goto_model, get_message_handler()))
        return true;
        
      config.ansi_c.set_from_symbol_table(goto_model.symbol_table);

      if(cmdline.isset("show-symbol-table"))
      {
        show_symbol_table();
        return true;
      }
      
      irep_idt entry_point=goto_model.goto_functions.entry_point();
      
      if(goto_model.symbol_table.symbols.find(entry_point)==symbol_table.symbols.end())
      {
        error() << "The goto binary has no entry point; please complete linking" << eom;
        return true;
      }
    }
    else if(cmdline.isset("show-parse-tree"))
    {
      if(cmdline.args.size()!=1)
      {
        error() << "Please give one source file only" << eom;
        return true;
      }
      
      std::string filename=cmdline.args[0];
      
      #ifdef _MSC_VER
      std::ifstream infile(widen(filename).c_str());
      #else
      std::ifstream infile(filename.c_str());
      #endif
                
      if(!infile)
      {
        error() << "failed to open input file `" << filename << "'" << eom;
        return true;
      }
                              
      languaget *language=get_language_from_filename(filename);
                                                
      if(language==NULL)
      {
        error() << "failed to figure out type of file `" <<  filename << "'" << eom;
        return true;
      }
      
      language->set_message_handler(get_message_handler());
                                                                
      status("Parsing", filename);
  
      if(language->parse(infile, filename))
      {
        error() << "PARSING ERROR" << eom;
        return true;
      }
      
      language->show_parse(std::cout);
      return true;
    }
    else
    {
    
      if(parse()) return true;
      if(typecheck()) return true;
      if(final()) return true;

      // we no longer need any parse trees or language files
      clear_parse();

      if(cmdline.isset("show-symbol-table"))
      {
        show_symbol_table();
        return true;
      }

      irep_idt entry_point=goto_model.goto_functions.entry_point();
      
      if(symbol_table.symbols.find(entry_point)==symbol_table.symbols.end())
      {
        error() << "No entry point; please provide a main function" << eom;
        return true;
      }
      
      status() << "Generating GOTO Program" << eom;

      goto_convert(symbol_table, goto_model, ui_message_handler);
    }

    // finally add the library
    status() << "Adding CPROVER library" << eom;
    link_to_library(goto_model, ui_message_handler);

    if(process_goto_program(options, goto_model))
      return true;
  }

  catch(const char *e)
  {
    error(e);
    return true;
  }

  catch(const std::string e)
  {
    error(e);
    return true;
  }
  
  catch(int)
  {
    return true;
  }
  
  catch(std::bad_alloc)
  {
    error() << "Out of memory" << eom;
    return true;
  }
  
  return false;
}

/*******************************************************************\

Function: summarizer_parseoptionst::process_goto_program

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
  
bool summarizer_parseoptionst::process_goto_program(
  const optionst &options,
  goto_modelt &goto_model)
{
  try
  {
    // do partial inlining
    status() << "Partial Inlining" << eom;
    goto_partial_inline(goto_model, ui_message_handler);
    
    // add generic checks
    status() << "Generic Property Instrumentation" << eom;
    goto_check(options, goto_model);

    // remove returns
    remove_returns(goto_model);
    
    // recalculate numbers, etc.
    goto_model.goto_functions.update();

    // add loop ids
    goto_model.goto_functions.compute_loop_numbers();
    

    // if we aim to cover, replace
    // all assertions by false to prevent simplification
    
    if(cmdline.isset("cover-assertions"))
      make_assertions_false(goto_model);

    // show it?
    if(cmdline.isset("show-loops"))
    {
      show_loop_ids(get_ui(), goto_model);
      return true;
    }

    status() << "Function Pointer Removal" << eom;
    remove_function_pointers(
      goto_model, cmdline.isset("pointer-check"));

    // now do full inlining, if requested

    if(cmdline.isset("inline"))
    {
      status() << "Performing full inlining" << eom;
      goto_inline(goto_model, ui_message_handler);
    }

    //inline c::__CPROVER_initialize and c::main
    if(cmdline.isset("inline-main"))
    {
      inline_main(goto_model); 
    }

    label_properties(goto_model);

    if(cmdline.isset("show-properties"))
    {
      show_properties(goto_model, get_ui());
      return true;
    }

    if(set_properties(goto_model))
      return true;

    // show it?
    if(cmdline.isset("show-goto-functions"))
    {
      const namespacet ns(goto_model.symbol_table);
      goto_model.goto_functions.output(ns, std::cout);
      return true;
    }
  }

  catch(const char *e)
  {
    error(e);
    return true;
  }

  catch(const std::string e)
  {
    error(e);
    return true;
  }
  
  catch(int)
  {
    return true;
  }
  
  catch(std::bad_alloc)
  {
    error() << "Out of memory" << eom;
    return true;
  }
  
  return false;
}

/*******************************************************************\

Function: summarizer_parseoptionst::inline_main

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarizer_parseoptionst::inline_main(goto_modelt &goto_model)
{
  goto_programt &main = goto_model.goto_functions.function_map[ID_main].body;
  goto_programt::targett target = main.instructions.begin();
  while(target!=main.instructions.end())
  {
    if(target->is_function_call())
    {
      const code_function_callt &code_function_call=
        to_code_function_call(target->code);
      irep_idt fname = code_function_call.function().get(ID_identifier); 

      debug() << "Inlining " << fname << eom;

      goto_programt tmp;
      tmp.copy_from(goto_model.goto_functions.function_map[fname].body);
      (--tmp.instructions.end())->make_skip();
      goto_model.goto_functions.function_map.erase(fname);
    
      goto_programt::targett next_target(target);
      target->make_skip();
      next_target++;
      main.instructions.splice(next_target, tmp.instructions);
      target=next_target;
    }
    else target++;
  }

  goto_model.goto_functions.update();
  goto_model.goto_functions.compute_loop_numbers();
}

/*******************************************************************\

Function: summarizer_parseoptionst::report_properties

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarizer_parseoptionst::report_properties(
  const goto_modelt &goto_model,
  const property_checkert::property_mapt &property_map)
{
  for(property_checkert::property_mapt::const_iterator
      it=property_map.begin();
      it!=property_map.end();
      it++)
  {
    if(get_ui()==ui_message_handlert::XML_UI)
    {
      xmlt xml_result("result");
      xml_result.set_attribute("property", id2string(it->first));
      xml_result.set_attribute("status", property_checkert::as_string(it->second.result));
      std::cout << xml_result << "\n";
    }
    else
    {
      status() << "[" << it->first << "] "
               << it->second.location->location.get_comment()
               << ": "
               << property_checkert::as_string(it->second.result)
               << eom;
    }

    if(cmdline.isset("show-trace") &&
       it->second.result==property_checkert::FAIL)
      show_counterexample(goto_model, it->second.error_trace);
  }

  if(!cmdline.isset("property"))
  {
    status() << eom;

    unsigned failed=0;

    for(property_checkert::property_mapt::const_iterator
        it=property_map.begin();
        it!=property_map.end();
        it++)
      if(it->second.result==property_checkert::FAIL)
        failed++;
    
    status() << "** " << failed
             << " of " << property_map.size() << " failed"
             << eom;  
  }
}

/*******************************************************************\

Function: summarizer_parseoptionst::report_success

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarizer_parseoptionst::report_success()
{
  result() << "VERIFICATION SUCCESSFUL" << eom;

  switch(get_ui())
  {
  case ui_message_handlert::PLAIN:
    break;
    
  case ui_message_handlert::XML_UI:
    {
      xmlt xml("cprover-status");
      xml.data="SUCCESS";
      std::cout << xml;
      std::cout << std::endl;
    }
    break;
    
  default:
    assert(false);
  }
}

/*******************************************************************\

Function: summarizer_parseoptionst::show_counterexample

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarizer_parseoptionst::show_counterexample(
  const goto_modelt &goto_model,
  const goto_tracet &error_trace)
{
  const namespacet ns(goto_model.symbol_table);

  switch(get_ui())
  {
  case ui_message_handlert::PLAIN:
    std::cout << std::endl << "Counterexample:" << std::endl;
    show_goto_trace(std::cout, ns, error_trace);
    break;
  
  case ui_message_handlert::XML_UI:
    {
      xmlt xml;
      convert(ns, error_trace, xml);
      std::cout << xml << std::endl;
    }
    break;
  
  default:
    assert(false);
  }
}

/*******************************************************************\

Function: summarizer_parseoptionst::report_failure

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarizer_parseoptionst::report_failure()
{
  result() << "VERIFICATION FAILED" << eom;

  switch(get_ui())
  {
  case ui_message_handlert::PLAIN:
    break;
    
  case ui_message_handlert::XML_UI:
    {
      xmlt xml("cprover-status");
      xml.data="FAILURE";
      std::cout << xml;
      std::cout << std::endl;
    }
    break;
    
  default:
    assert(false);
  }
}

/*******************************************************************\

Function: summarizer_parseoptionst::help

  Inputs:

 Outputs:

 Purpose: display command line help

\*******************************************************************/

void summarizer_parseoptionst::help()
{
  std::cout <<
    "\n"
    "* *  Summarizer " CBMC_VERSION " - Copyright (C) 2014 ";
    
  std::cout << "(" << (sizeof(void *)*8) << "-bit version)";
    
  std::cout << "   * *\n";
    
  std::cout <<
    "* *                    Daniel Kroening                      * *\n"
    "* *                 University of Oxford                    * *\n"
    "* *                 kroening@kroening.com                   * *\n"
    "\n"
    "Usage:                       Purpose:\n"
    "\n"
    " summarizer [-?] [-h] [--help] show help\n"
    " summarizer file.c ...        source file names\n"
    "\n"
    "Frontend options:\n"
    " -I path                      set include path (C/C++)\n"
    " -D macro                     define preprocessor macro (C/C++)\n"
    " --preprocess                 stop after preprocessing\n"
    " --16, --32, --64             set width of int\n"
    " --LP64, --ILP64, --LLP64,\n"
    "   --ILP32, --LP32            set width of int, long and pointers\n"
    " --little-endian              allow little-endian word-byte conversions\n"
    " --big-endian                 allow big-endian word-byte conversions\n"
    " --unsigned-char              make \"char\" unsigned by default\n"
    " --show-stats                 show statistics about program\n"
    " --show-parse-tree            show parse tree\n"
    " --show-symbol-table          show symbol table\n"
    " --show-goto-functions        show goto program\n"
    " --arch                       set architecture (default: "
                                   << configt::this_architecture() << ")\n"
    " --os                         set operating system (default: "
                                   << configt::this_operating_system() << ")\n"
    #ifdef _WIN32
    " --gcc                        use GCC as preprocessor\n"
    #endif
    " --no-arch                    don't set up an architecture\n"
    " --no-library                 disable built-in abstract C library\n"
    " --round-to-nearest           IEEE floating point rounding mode (default)\n"
    " --round-to-plus-inf          IEEE floating point rounding mode\n"
    " --round-to-minus-inf         IEEE floating point rounding mode\n"
    " --round-to-zero              IEEE floating point rounding mode\n"
    "\n"
    "Program instrumentation options:\n"
    " --bounds-check               enable array bounds checks\n"
    " --div-by-zero-check          enable division by zero checks\n"
    " --pointer-check              enable pointer checks\n"
    " --memory-leak-check          enable memory leak checks\n"
    " --signed-overflow-check      enable arithmetic over- and underflow checks\n"
    " --unsigned-overflow-check    enable arithmetic over- and underflow checks\n"
    " --nan-check                  check floating-point for NaN\n"
    " --error-label label          check that label is unreachable\n"
    " --show-properties            show the properties\n"
    " --no-assertions              ignore user assertions\n"
    " --no-assumptions             ignore user assumptions\n"
    " --inline                     inline all functions into main\n"
    "\n"
    "Backend options:\n"
    " --context-sensitive          context-sensitive analysis from entry point\n"
    " --havoc                      havoc loops and function calls\n"
    " --intervals                  use interval domain\n"
    " --equalities                 use equalities and disequalities domain\n"
    " --zones                      use zone domain\n"
    " --octagons                   use octagon domain\n"
    " --enum-solver                use solver based on model enumeration\n"
    " --binsearch-solver           use solver based on binary search\n"
    " --arrays                     do not ignore array contents\n"
    "\n"
    "Other options:\n"
    " --version                    show version and exit\n"
    " --xml-ui                     use XML-formatted output\n"
    "\n";
}
