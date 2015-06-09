/*******************************************************************\

Module: Command Line Interface

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cstdlib>

#include <iostream>

#include <util/string2int.h>

#include "../deltacheck/version.h"

#include "show_jobs.h"
#include "do_job.h"
#include "init.h"
#include "reset.h"
#include "reanalyse.h"
#include "deltagit_parse_options.h"
#include "revisions_report.h"

/*******************************************************************\

Function: deltagit_parse_optionst::deltagit_parse_optionst

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

deltagit_parse_optionst::deltagit_parse_optionst(
  int argc, const char **argv):
  parse_options_baset(DELTACHECK_OPTIONS, argc, argv)
{
}
  
/*******************************************************************\

Function: deltagit_parse_optionst::doit

  Inputs:

 Outputs:

 Purpose: invoke main modules

\*******************************************************************/

int deltagit_parse_optionst::doit()
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
        reset(cmdline.args[1]);
      else if(cmdline.args.size()==1)
        reset();
      else
      {
        usage_error();
        return 10;
      }
    }
    else if(command=="reanalyse")
    {
      if(cmdline.args.size()==2)
        reanalyse(cmdline.args[1]);
      else if(cmdline.args.size()==1)
        reanalyse();
      else
      {
        usage_error();
        return 10;
      }
    }
    else if(command=="report")
    {
      bool partial_html=cmdline.isset("partial-html");
      unsigned max_revs=0;
      std::string rel_path;
      if(cmdline.isset("max-revs"))
        max_revs=unsafe_string2unsigned(cmdline.get_value("max-revs"));
      if(partial_html)
        rel_path=cmdline.get_value("partial-html");
      revisions_report(partial_html, rel_path, max_revs);
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

Function: deltagit_parse_optionst::help

  Inputs:

 Outputs:

 Purpose: display command line help

\*******************************************************************/

void deltagit_parse_optionst::help()
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
    " deltagit reanalyse           redo analysis\n"
    " deltagit report              generate top-level report\n"
    "\n"
    "Reporting options:\n"
    " --partial-html               generate a partial HTML file \"include.html\"\n"
    " --max-revs <nr>              report on the last <nr> revisions\n"
    "\n"    
    "Other options:\n"
    " --version                    show version and exit\n"
    " --xml-ui                     use XML-formatted output\n"
    "\n";
}
