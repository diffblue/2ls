/*******************************************************************\

Module: Command Line Interface

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iostream>

#if 0
#include <cstdlib>
#include <fstream>
#include <memory>

#include <util/i2string.h>
#include <util/config.h>
#include <util/symbol_table.h>

#include <langapi/mode.h>
#include <cbmc/version.h>
#include <ansi-c/ansi_c_language.h>
#include <cpp/cpp_language.h>

#include "index.h"
#include "analyzer.h"
#include "show.h"
#include "versioning.h"
#endif

#include "../deltacheck/version.h"

#include "init.h"
#include "show_jobs.h"
#include "update.h"

#include "deltarepo_parseoptions.h"

/*******************************************************************\

Function: deltarepo_parseoptionst::deltarepo_parseoptionst

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

deltarepo_parseoptionst::deltarepo_parseoptionst(
  int argc, const char **argv):
  parseoptions_baset(DELTACHECK_OPTIONS, argc, argv)
{
}
  
/*******************************************************************\

Function: deltarepo_parseoptionst::doit

  Inputs:

 Outputs:

 Purpose: invoke main modules

\*******************************************************************/

int deltarepo_parseoptionst::doit()
{
  if(cmdline.isset("version"))
  {
    std::cout << DELTACHECK_VERSION << std::endl;
    return 0;
  }

  try
  {
    if(cmdline.args.size()==0)
    {
      usage_error();
      return 10;
    }
    
    const std::string command=cmdline.args[0];
    
    if(command=="init-git")
    {
      if(cmdline.args.size()!=3)
      {
        usage_error();
        return 10;
      }
      
      init(GIT, cmdline.args[1], cmdline.args[2]);
    }
    else if(command=="init-svn")
    {
      if(cmdline.args.size()!=3)
      {
        usage_error();
        return 10;
      }
      
      init(SVN, cmdline.args[1], cmdline.args[2]);
    }
    else if(command=="update")
    {
      update();
    }
    else if(command=="jobs")
    {
      show_jobs();
    }
    else
    {
      usage_error();
      return 10;
    }
  }

  catch(const std::string &e)
  {
    std::cerr << e << std::endl;
    return 13;
  }
  
  catch(std::bad_alloc)
  {
    std::cerr << "Out of memory" << std::endl;
    return 14;
  }
  
  return 0;
}

/*******************************************************************\

Function: deltarepo_parseoptionst::help

  Inputs:

 Outputs:

 Purpose: display command line help

\*******************************************************************/

void deltarepo_parseoptionst::help()
{
  std::cout <<
    "\n"
    "* *         DELTAREPO " DELTACHECK_VERSION " - Copyright (C) 2011-2013        * *\n"
    "* *                     Daniel Kroening                     * *\n"
    "* *      Oxford University, Computer Science Department     * *\n"
    "* *                 kroening@kroening.com                   * *\n"
    "\n"
    "Usage:                       Purpose:\n"
    "\n"
    " deltarepo [-?] [-h] [--help] show help\n"
    " deltarepo init-svn url dest  set up svn clone in given directory dest\n"
    " deltarepo init-git url dest  set up git clone in given directory dest\n"
    " deltarepo update             update current directory\n"
    " deltarepo jobs               list the jobs for the current directory\n"
    "\n"    
    "Other options:\n"
    " --version                    show version and exit\n"
    " --xml-ui                     use XML-formatted output\n"
    " --xml-interface              stdio-XML interface\n"
    "\n";
}
