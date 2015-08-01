/*******************************************************************\

Module: Command Line Interface

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cstdlib>
#include <fstream>
#include <memory>
#include <iostream>

#include <util/config.h>
#include <util/symbol_table.h>
#include <util/string2int.h>

#include <langapi/mode.h>
#include <cbmc/version.h>
#include <ansi-c/ansi_c_language.h>
#include <cpp/cpp_language.h>
#include <goto-programs/read_goto_binary.h>

#include "deltacheck_parse_options.h"
#include "version.h"
#include "analyzer.h"
#include "change_impact.h"
#include "../functions/path_util.h"

/*******************************************************************\

Function: deltacheck_parse_optionst::deltacheck_parse_optionst

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

deltacheck_parse_optionst::deltacheck_parse_optionst(
  int argc, const char **argv):
  parse_options_baset(DELTACHECK_OPTIONS, argc, argv),
  xml_interfacet(cmdline),
  ui_message_handler(
    cmdline.isset("xml-ui")?ui_message_handlert::XML_UI:ui_message_handlert::PLAIN,
    "DeltaCheck " DELTACHECK_VERSION)
{
}
  
/*******************************************************************\

Function: deltacheck_parse_optionst::eval_verbosity

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void deltacheck_parse_optionst::eval_verbosity()
{
  // our default verbosity
  int v=messaget::M_STATISTICS;
  
  if(cmdline.isset("verbosity"))
  {
    v=unsafe_string2int(cmdline.get_value("verbosity"));
    if(v<0)
      v=0;
    else if(v>10)
      v=10;
  }
  
  ui_message_handler.set_verbosity(v);
}

/*******************************************************************\

Function: deltacheck_parse_optionst::get_command_line_options

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void deltacheck_parse_optionst::get_command_line_options(optionst &options)
{
  if(config.set(cmdline))
  {
    usage_error();
    exit(1);
  }

  if(cmdline.isset("debug-level"))
    options.set_option("debug-level", cmdline.get_value("debug-level"));

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

  // do we do inlining?
  if(cmdline.isset("no-inlining"))
    options.set_option("partial-inlining", false);
  else
    options.set_option("partial-inlining", true);

  // check assertions
  options.set_option("assertions", true);

  // use assumptions
  options.set_option("assumptions", true);
}

/*******************************************************************\

Function: deltacheck_parse_optionst::register_langauges

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void deltacheck_parse_optionst::register_languages()
{
  register_language(new_ansi_c_language);
  register_language(new_cpp_language);
}

/*******************************************************************\

Function: deltacheck_parse_optionst::doit

  Inputs:

 Outputs:

 Purpose: invoke main modules

\*******************************************************************/

int deltacheck_parse_optionst::doit()
{
  if(cmdline.isset("version"))
  {
    std::cout << DELTACHECK_VERSION << std::endl;
    return 0;
  }

  register_languages();

  // command line options

  optionst options;
  get_command_line_options(options);
  set_message_handler(ui_message_handler);
  eval_verbosity();

  try
  {
    options.set_option("simplify", true);
    options.set_option("assertions", true);
    options.set_option("assumptions", true);
    
    if(cmdline.isset("function"))
      options.set_option("function", cmdline.get_value("function"));
    
    if(cmdline.args.size()!=2)
    {
      usage_error();
      return 10;
    }

    if(cmdline.isset("description-old"))
      options.set_option("description-old", cmdline.get_value("description-old"));
    else
      options.set_option("description-old", cmdline.args[0]);
    
    if(cmdline.isset("description-new"))
      options.set_option("description-new", cmdline.get_value("description-new"));
    else
      options.set_option("description-new", cmdline.args[1]);
    
    status() << "Reading first GOTO program from file" << eom;
    
    goto_modelt goto_model1;

    if(read_goto_binary(cmdline.args[0],
         goto_model1, get_message_handler()))
      return 10;
      
    status() << "Reading second GOTO program from file" << eom;
    
    goto_modelt goto_model2;

    if(read_goto_binary(cmdline.args[1],
         goto_model2, get_message_handler()))
      return 10;
      
    if(cmdline.isset("show-diff"))
    {
      change_impactt change_impact;
      change_impact.set_message_handler(get_message_handler());
    
      change_impact.diff(goto_model1, goto_model2);
      change_impact.output_diff(std::cout);
    }
    else if(cmdline.isset("show-change-impact"))
    {
      change_impactt change_impact;
      change_impact.set_message_handler(get_message_handler());
    
      status() << "Computing syntactic difference" << eom;
      change_impact.diff(goto_model1, goto_model2);

      status() << "Change-impact analysis" << eom;
      change_impact.change_impact(goto_model2);

      change_impact.output_change_impact(std::cout);
    }
    else
    {
      std::string path1=get_directory(cmdline.args[0]);
      std::string path2=get_directory(cmdline.args[1]);
    
      deltacheck_analyzer(
        path1, goto_model1,
        path2, goto_model2,
        options, get_message_handler());
    }
    
    return 0;
  }

  catch(const char *e)
  {
    error() << e << eom;
    return 13;
  }

  catch(const std::string &e)
  {
    error() << e << eom;
    return 13;
  }
  
  catch(int)
  {
    return 13;
  }
  
  catch(std::bad_alloc)
  {
    error() << "Out of memory" << eom;
    return 14;
  }
  
  return 0;
}

/*******************************************************************\

Function: deltacheck_parse_optionst::help

  Inputs:

 Outputs:

 Purpose: display command line help

\*******************************************************************/

void deltacheck_parse_optionst::help()
{
  std::cout <<
    "\n"
    "* *         DELTACHECK " DELTACHECK_VERSION " - Copyright (C) 2011-2015        * *\n"
    "* *                    based on CBMC " CBMC_VERSION "                    * *\n"
    "* *                     Daniel Kroening                     * *\n"
    "* *      Oxford University, Computer Science Department     * *\n"
    "* *                 kroening@kroening.com                   * *\n"
    "\n"
    "Usage:                       Purpose:\n"
    "\n"
    " deltacheck [-?] [-h] [--help] show help\n"
    " deltacheck prog1 prog2       delta check two programs\n"
    "\n"
    "Delta checking options:\n"
    " --show-change-impact         show syntactic change-impact\n"
    " --description-old text       description of old version\n"
    " --description-new text       description of new version\n"
    "\n"
    "Safety checks:\n"
    " --bounds-check               add array bounds checks\n"
    " --div-by-zero-check          add division by zero checks\n"
    " --pointer-check              add pointer checks\n"
    " --signed-overflow-check      add arithmetic over- and underflow checks\n"
    " --unsigned-overflow-check    add arithmetic over- and underflow checks\n"
    " --nan-check                  add floating-point NaN checks\n"    
    "\n"    
    "Other options:\n"
    " --version                    show version and exit\n"
    " --xml-ui                     use XML-formatted output\n"
    " --xml-interface              stdio-XML interface\n"
    "\n";
}
