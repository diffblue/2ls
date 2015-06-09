/*******************************************************************\

Module: Command Line Interface

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_DELTACHECK_PARSEOPTIONS_H
#define CPROVER_DELTACHECK_PARSEOPTIONS_H

#include <util/parse_options.h>

#define STOREFRONT_OPTIONS \
  "(verbosity):(version)"

class storefront_parse_optionst:public parse_options_baset
{
public:
  virtual int doit();
  virtual void help();

  storefront_parse_optionst(
    int argc, const char **argv);

protected:
};

#endif
