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

#include "../functions/index.h"
#include "deltacheck_parseoptions.h"
#include "version.h"
#include "analyzer.h"
#include "change_impact.h"
#include "show.h"

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

Function: deltacheck_parseoptionst::eval_verbosity

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void deltacheck_parseoptionst::eval_verbosity()
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
  
  set_verbosity(v);
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
  set_message_handler(ui_message_handler);
  eval_verbosity();

  try
  {
    // We have two phases:
    // 1) indexing: given some goto-binaries, produce index
    // 2) delta checking: given two indices, do delta checking
    
    if(cmdline.isset("index"))
    {
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
      
      indext index;
      index.set_message_handler(get_message_handler());

      if(cmdline.args.size()==0)
      {
        // read from stdin
        std::vector<std::string> files;
        std::string line;
        while(std::getline(std::cin, line))
        {
          if(!line.empty())
            files.push_back(line);
        }

        index.build(files, description);
      }
      else
        index.build(cmdline.args, description);

      index.write(out);
      return 0;
    }
    
    options.set_option("simplify", true);
    options.set_option("assertions", true);
    options.set_option("assumptions", true);
    
    if(cmdline.isset("show-ssa"))
    {
      if(cmdline.args.size()!=1)
      {
        usage_error();
        return 10;
      }

      indext index;
      index.set_message_handler(get_message_handler());
  
      status() << "Reading index" << eom;
      index.read(cmdline.args[0]);

      show_ssa(index, options, std::cout, get_message_handler());
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
      index.set_message_handler(get_message_handler());
      index.read(cmdline.args[0]);

      show_defs(index, options, std::cout, get_message_handler());
      return 0;
    }

    if(cmdline.isset("show-guards"))
    {
      if(cmdline.args.size()!=1)
      {
        usage_error();
        return 10;
      }

      indext index;
      index.set_message_handler(get_message_handler());
      index.read(cmdline.args[0]);

      show_guards(index, options, std::cout, get_message_handler());
      return 0;
    }

    if(cmdline.isset("show-fixed-points"))
    {
      if(cmdline.args.size()!=1)
      {
        usage_error();
        return 10;
      }

      indext index;
      index.set_message_handler(get_message_handler());
      index.read(cmdline.args[0]);

      show_fixed_points(index, options, std::cout, get_message_handler());
      return 0;
    }

    if(cmdline.isset("show-properties"))
    {
      if(cmdline.args.size()!=1)
      {
        usage_error();
        return 10;
      }

      indext index;
      index.set_message_handler(get_message_handler());
  
      status() << "Reading index" << eom;
      index.read(cmdline.args[0]);

      show_properties(index, options, std::cout, get_message_handler());
      return 0;
    }

    if(cmdline.isset("show-diff"))
    {
      if(cmdline.args.size()!=2)
      {
        usage_error();
        return 10;
      }

      indext index1, index2;
      index1.set_message_handler(get_message_handler());
      index2.set_message_handler(get_message_handler());
  
      index1.read(cmdline.args[0]);
      index2.read(cmdline.args[1]);

      change_impactt change_impact;
      change_impact.set_message_handler(get_message_handler());
      
      change_impact.diff(index1, index2);
      change_impact.output_diff(std::cout);

      return 0;
    }
    
    if(cmdline.isset("show-change-impact"))
    {
      if(cmdline.args.size()!=2)
      {
        usage_error();
        return 10;
      }

      indext index1, index2;
      index1.set_message_handler(get_message_handler());
      index2.set_message_handler(get_message_handler());
  
      index1.read(cmdline.args[0]);
      index2.read(cmdline.args[1]);

      change_impactt change_impact;
      change_impact.set_message_handler(get_message_handler());
      
      status() << "Computing syntactic difference" << eom;
      change_impact.diff(index1, index2);

      status() << "Change-impact analysis" << eom;
      change_impact.change_impact(index2);

      change_impact.output_change_impact(std::cout);

      return 0;
    }
    
    if(cmdline.args.size()==2)
    {
      indext index1, index2;
      index1.set_message_handler(get_message_handler());
      index2.set_message_handler(get_message_handler());
  
      index1.read(cmdline.args[0]);
      index2.read(cmdline.args[1]);

      deltacheck_analyzer(index1, index2, options, get_message_handler());
    }
    else if(cmdline.args.size()==1)
    {
      indext index;
      index.set_message_handler(get_message_handler());
  
      index.read(cmdline.args[0]);

      one_program_analyzer(index, options, get_message_handler());
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
    "* *         DELTACHECK " DELTACHECK_VERSION " - Copyright (C) 2011-2014        * *\n"
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
    " deltacheck --index           \n"
    "   index-file.xml < list      build index for files given as list\n"
    " deltacheck index1 index2     delta check two versions\n"
    "\n"
    "Indexing options:\n"
    "\n"
    "Delta checking options:\n"
    " --show-ssa                   show SSA\n"
    " --show-guards                show guards\n"
    " --show-properties            show the properties\n"
    " --show-fixed-points          show the fixed-points for the loops\n"
    " --show-change-impact         show syntactic change-impact\n"
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
