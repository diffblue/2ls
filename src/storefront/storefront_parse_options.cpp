/*******************************************************************\

Module: Command Line Interface

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iostream>

#include "../deltacheck/version.h"

#include "storefront_parse_options.h"

/*******************************************************************\

Function: storefront_parse_optionst::storefront_parse_optionst

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

storefront_parse_optionst::storefront_parse_optionst(
  int argc, const char **argv):
  parse_options_baset(STOREFRONT_OPTIONS, argc, argv)
{
}
  
/*******************************************************************\

Function: storefront_parse_optionst::doit

  Inputs:

 Outputs:

 Purpose: invoke main modules

\*******************************************************************/

int storefront_parse_optionst::doit()
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

Function: storefront_parse_optionst::help

  Inputs:

 Outputs:

 Purpose: display command line help

\*******************************************************************/

void storefront_parse_optionst::help()
{
  std::cout <<
    "\n"
    "* *          STOREFRONT " DELTACHECK_VERSION " - Copyright (C) 2014-2015        * *\n"
    "* *                     Daniel Kroening                     * *\n"
    "* *      Oxford University, Computer Science Department     * *\n"
    "* *                 kroening@kroening.com                   * *\n"
    "\n"
    "Usage:                       Purpose:\n"
    "\n"
    " storefront [-?] [-h] [--help] show help\n"
    " storefront config.xml        generate pages\n"
    "\n"
    "Other options:\n"
    " --version                    show version and exit\n"
    "\n";
}
