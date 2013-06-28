/*******************************************************************\

Module: Command Line Interface

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cstdlib>
#include <fstream>
#include <memory>
#include <iostream>

#include <util/i2string.h>
#include <util/config.h>
#include <util/symbol_table.h>

#include <langapi/mode.h>
#include <cbmc/version.h>
#include <ansi-c/ansi_c_language.h>
#include <cpp/cpp_language.h>

#include "deltacheck_parseoptions.h"
#include "version.h"
#include "index.h"
#include "delta_check.h"
#include "one_program_check.h"
#include "show_ssa.h"
#include "show_defs.h"

/*******************************************************************\

Function: deltacheck_parseoptionst::deltacheck_parseoptionst

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

deltacheck_parseoptionst::deltacheck_parseoptionst(
  int argc, const char **argv):
  parseoptions_baset(DELTACHECK_OPTIONS, argc, argv),
  xml_interfacet(cmdline),
  ui_message_handler(
    cmdline.isset("xml-ui")?ui_message_handlert::XML_UI:ui_message_handlert::PLAIN,
    "DeltaCheck " DELTACHECK_VERSION)
{
}
  
/*******************************************************************\

Function: deltacheck_parseoptionst::set_verbosity

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void deltacheck_parseoptionst::set_verbosity(messaget &message)
{
  // our default verbosity
  int v=messaget::M_STATISTICS;
  
  if(cmdline.isset("verbosity"))
  {
    v=atoi(cmdline.getval("verbosity"));
    if(v<0)
      v=0;
    else if(v>10)
      v=10;
  }
  
  message.set_verbosity(v);
}

/*******************************************************************\

Function: deltacheck_parseoptionst::get_command_line_options

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void deltacheck_parseoptionst::get_command_line_options(optionst &options)
{
  if(config.set(cmdline))
  {
    usage_error();
    exit(1);
  }

  if(cmdline.isset("debug-level"))
    options.set_option("debug-level", cmdline.getval("debug-level"));

  #if 0
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
  #else
  options.set_option("bounds-check", true);
  options.set_option("div-by-zero-check", true);
  options.set_option("signed-overflow-check", true);
  options.set_option("unsigned-overflow-check", false);
  options.set_option("pointer-check", true);
  #endif

  // check assertions
  options.set_option("assertions", true);

  // use assumptions
  options.set_option("assumptions", true);
}

/*******************************************************************\

Function: deltacheck_parseoptionst::register_langauges

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void deltacheck_parseoptionst::register_languages()
{
  register_language(new_ansi_c_language);
  register_language(new_cpp_language);
}

/*******************************************************************\

Function: deltacheck_parseoptionst::doit

  Inputs:

 Outputs:

 Purpose: invoke main modules

\*******************************************************************/

int deltacheck_parseoptionst::doit()
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
  set_verbosity(*this);
  set_message_handler(ui_message_handler);

  try
  {
    // We have two phases:
    // 1) indexing: given some goto-binaries, produce index
    // 2) delta checking: given two indices, do delta checking

    if(cmdline.isset("index"))
    {
      if(cmdline.args.size()==0)
      {
        usage_error();
        return 10;
      }
      
      status() << "Building index `" << cmdline.getval("index") << "'" << eom;
      
      std::ofstream out(cmdline.getval("index"));
      if(!out)
      {
        error() << "failed to open output file `"
                << cmdline.getval("index") << "' " << eom;
        return 11;
      }
      
      std::string description;
      if(cmdline.isset("description"))
        description=cmdline.getval("description");
      
      build_index(cmdline.args, description, out, get_message_handler());
      return 0;
    }
    
    if(cmdline.isset("show-ssa"))
    {
      if(cmdline.args.size()!=1)
      {
        usage_error();
        return 10;
      }

      indext index;
  
      status() << "Reading index" << eom;
      index.read(cmdline.args[0], get_message_handler());

      show_ssa(index, std::cout, get_message_handler());
      return 0;
    }

    if(cmdline.isset("show-defs"))
    {
      if(cmdline.args.size()!=1)
      {
        usage_error();
        return 10;
      }

      indext index;
  
      status() << "Reading index" << eom;
      index.read(cmdline.args[0], get_message_handler());

      show_defs(index, std::cout, get_message_handler());
      return 0;
    }

    if(cmdline.args.size()==2)
    {
      std::string function;
      if(cmdline.isset("function"))
        function=cmdline.getval("function");

      indext index1, index2;
  
      status() << "Reading first index" << eom;
      index1.read(cmdline.args[0], get_message_handler());

      status() << "Reading second index" << eom;
      index2.read(cmdline.args[1], get_message_handler());

      delta_check(index1, index2, function, get_message_handler());
    }
    else if(cmdline.args.size()==1)
    {
      std::string function;
      if(cmdline.isset("function"))
        function=cmdline.getval("function");
    
      indext index;
  
      status() << "Reading index" << eom;
      index.read(cmdline.args[0], get_message_handler());

      simple_check(index, function, get_message_handler());
    }
    else
    {
      usage_error();
      return 10;
    }
  }

  catch(const char *e)
  {
    error(e);
    return 13;
  }

  catch(const std::string &e)
  {
    error(e);
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

Function: deltacheck_parseoptionst::help

  Inputs:

 Outputs:

 Purpose: display command line help

\*******************************************************************/

void deltacheck_parseoptionst::help()
{
  std::cout <<
    "\n"
    "* *         DELTACHECK " DELTACHECK_VERSION " - Copyright (C) 2011-2013        * *\n"
    "* *                    based on CBMC " CBMC_VERSION "                    * *\n"
    "* *                     Daniel Kroening                     * *\n"
    "* *      Oxford University, Computer Science Department     * *\n"
    "* *                 kroening@kroening.com                   * *\n"
    "\n"
    "Usage:                       Purpose:\n"
    "\n"
    " deltacheck [-?] [-h] [--help] show help\n"
    " deltacheck --index           \n"
    "   index-file.xml file(s)     build index for given file(s)\n"
    " deltacheck index1 index2     delta check two versions\n"
    "\n"
    "Indexing options:\n"
    "\n"
    "Delta checking options:\n"
    " --function id                limit analysis to given function\n"
    " --show-ssa                   show SSA\n"
    "\n"    
    "Other options:\n"
    " --version                    show version and exit\n"
    " --xml-ui                     use XML-formatted output\n"
    " --xml-interface              stdio-XML interface\n"
    "\n";
}
