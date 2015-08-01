/*******************************************************************\

Module: Command Line Interface

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iostream>

#include "../deltacheck/version.h"

#include "storefront_parse_options.h"
#include "data.h"
#include "file_view.h"
#include "trace_view.h"
#include "property_view.h"

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
    if(cmdline.args.empty())
    {
      usage_error();
      return 10;
    }
    
    // read config
    datat data;
    
    for(unsigned i=0; i<cmdline.args.size(); i++)
      data.read(cmdline.args[i]);
    
    // write views
    file_view(data);
    property_view(data);
    trace_view(data);
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
