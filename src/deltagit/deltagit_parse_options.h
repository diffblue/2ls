/*******************************************************************\

Module: Command Line Interface

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_DELTACHECK_PARSE_OPTIONS_H
#define CPROVER_DELTACHECK_PARSE_OPTIONS_H

#include <util/parse_options.h>

#define DELTACHECK_OPTIONS \
  "(verbosity):(version)(description):" \
  "(max-revs):(partial-html):"

class deltagit_parse_optionst:public parse_options_baset
{
public:
  virtual int doit();
  virtual void help();

  deltagit_parse_optionst(
    int argc, const char **argv);

protected:
};

#endif
