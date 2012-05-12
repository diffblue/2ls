/*******************************************************************\

Module: Command Line Interface

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cstdlib>
#include <fstream>
#include <memory>
#include <iostream>

#include <config.h>
#include <context.h>

#include <langapi/mode.h>

#include <ansi-c/ansi_c_language.h>

#ifdef HAVE_CPP
#include <cpp/cpp_language.h>
#endif

#include "parseoptions.h"
#include "version.h"
#include "summarization.h"
#include "collation.h"

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
  int v=8;
  
  if(cmdline.isset("verbosity"))
  {
    v=atoi(cmdline.getval("verbosity"));
    if(v<0)
      v=0;
    else if(v>9)
      v=9;
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
  
  #ifdef HAVE_CPP
  register_language(new_cpp_language);
  #endif
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

  // We have two phases:
  // 1) summarization: given _one_ goto-binary, produce summary
  // 2) collation: put all summaries together
  //
  // The phases are distinguished by the type of input file.
  
  if(cmdline.args.size()==0)
  {
    usage_error();
    return 10;
  }
  
  if(cmdline.isset("summarize"))
    return summarization(options);
  else
    return collation(options);
}

/*******************************************************************\

Function: deltacheck_parseoptionst::summarization

  Inputs:

 Outputs:

 Purpose: summarize one goto binary

\*******************************************************************/

int deltacheck_parseoptionst::summarization(const optionst &options)
{
  try
  {
    for(cmdlinet::argst::const_iterator
        args_it=cmdline.args.begin();
        args_it!=cmdline.args.end();
        args_it++)
    {
      status("PHASE 1: Summarizing "+*args_it);
      
      ::summarization(cmdline.args[0], options, get_message_handler());
    }
  }

  catch(const char *e)
  {
    error(e);
    return 13;
  }

  catch(const std::string e)
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
    error("Out of memory");
    return 14;
  }
  
  return 0;
}

/*******************************************************************\

Function: deltacheck_parseoptionst::collation

  Inputs:

 Outputs:

 Purpose: collect and analyze the summaries

\*******************************************************************/

int deltacheck_parseoptionst::collation(const optionst &options)
{
  try
  {
    status("PHASE 2: Reading the list of files to collate");

    std::ifstream in(cmdline.args[0].c_str());

    if(!in)
    {
      error("failed to open file");
      return 12;
    }
    
    ::collation(in, options);
  }

  catch(const char *e)
  {
    error(e);
    return 13;
  }

  catch(const std::string e)
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
    error("Out of memory");
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
    "* *         DELTACHECK " DELTACHECK_VERSION " - Copyright (C) 2011-2012           * *\n"
    "* *                     Daniel Kroening                     * *\n"
    "* *      Oxford University, Computer Science Department     * *\n"
    "* *                 kroening@kroening.com                   * *\n"
    "\n"
    "Usage:                       Purpose:\n"
    "\n"
    " deltacheck [-?] [-h] [--help]   show help\n"
    " deltacheck file-list         collate information from given summaries (phase II)\n"
    "\n"
    "Phase I (summarization) options:\n"
    " --summarize files            summarize given goto-binaries\n"
    "\n"
    "Phase II (collation) options:\n"
    " --show-claims                show properties\n"
    " --claim id                   only check given claim\n"
    "\n"    
    "Other options:\n"
    " --version                    show version and exit\n"
    " --xml-ui                     use XML-formatted output\n"
    " --xml-interface              stdio-XML interface\n"
    "\n";
}
