/*******************************************************************\

Module: Command Line Interface

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cstdlib>

#include <iostream>

#include "../deltacheck/version.h"

#include "show_jobs.h"
#include "do_job.h"
#include "init.h"
#include "reset.h"
#include "deltagit_parseoptions.h"
#include "revisions_report.h"

/*******************************************************************\

Function: deltagit_parseoptionst::deltagit_parseoptionst

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

deltagit_parseoptionst::deltagit_parseoptionst(
  int argc, const char **argv):
  parseoptions_baset(DELTACHECK_OPTIONS, argc, argv)
{
}
  
/*******************************************************************\

Function: deltagit_parseoptionst::doit

  Inputs:

 Outputs:

 Purpose: invoke main modules

\*******************************************************************/

int deltagit_parseoptionst::doit()
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
    
    if(command=="jobs")
    {
      show_jobs(std::cout);
    }
    else if(command=="init")
    {
      if(cmdline.args.size()==1)
      {
        init(0);
      }
      else if(cmdline.args.size()==2)
      {
        init(atoi(cmdline.args[1].c_str()));
      }
      else
      {
        usage_error();
        return 10;
      }
    }
    else if(command=="do")
    {
      if(cmdline.args.size()==2)
      {
        do_job(cmdline.args[1]);
      }
      else if(cmdline.args.size()==1)
      {
        do_job();
      }
      else
      {
        usage_error();
        return 10;
      }
    }
    else if(command=="reset")
    {
      if(cmdline.args.size()==2)
      {
      }
      else if(cmdline.args.size()==1)
      {
        reset();
      }
      else
      {
        usage_error();
        return 10;
      }
    }
    else if(command=="report")
    {
      revisions_report();
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

Function: deltagit_parseoptionst::help

  Inputs:

 Outputs:

 Purpose: display command line help

\*******************************************************************/

void deltagit_parseoptionst::help()
{
  std::cout <<
    "\n"
    "* *           DELTAGIT " DELTACHECK_VERSION " - Copyright (C) 2012-2013        * *\n"
    "* *                     Daniel Kroening                     * *\n"
    "* *      Oxford University, Computer Science Department     * *\n"
    "* *                 kroening@kroening.com                   * *\n"
    "\n"
    "Usage:                       Purpose:\n"
    "\n"
    " deltagit [-?] [-h] [--help]  show help\n"
    " deltagit init <max-jobs>     set up the jobs\n"
    " deltagit jobs                list the jobs\n"
    " deltagit do <job>            do given job\n"
    " deltagit do                  do a job that needs work\n"
    " deltagit reset               clear failure bit on all jobs\n"
    " deltagit report              generate top-level report\n"
    "\n"    
    "Other options:\n"
    " --version                    show version and exit\n"
    " --xml-ui                     use XML-formatted output\n"
    "\n";
}
