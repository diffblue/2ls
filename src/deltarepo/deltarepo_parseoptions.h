/*******************************************************************\

Module: Command Line Interface

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_DELTACHECK_PARSEOPTIONS_H
#define CPROVER_DELTACHECK_PARSEOPTIONS_H

#include <util/parseoptions.h>

#define DELTACHECK_OPTIONS \
  "(verbosity):(version)(description):"

class deltarepo_parseoptionst:public parseoptions_baset
{
public:
  virtual int doit();
  virtual void help();

  deltarepo_parseoptionst(
    int argc, const char **argv);

protected:
};

#endif
