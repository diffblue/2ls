/*******************************************************************\

Module: Main Module 

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/unicode.h>

#include "deltarepo_parseoptions.h"

/*******************************************************************\

Function: main

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

#ifdef _MSC_VER
int wmain(int argc, const wchar_t **argv_wide)
{
  const char **argv=narrow_argv(argc, argv_wide);
  deltarepo_parseoptionst parseoptions(argc, argv);
  return parseoptions.main();
}
#else
int main(int argc, const char **argv)
{
  deltarepo_parseoptionst parseoptions(argc, argv);
  return parseoptions.main();
}
#endif
