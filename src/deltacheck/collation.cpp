/*******************************************************************\

Module: Collation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "collation.h"
#include "cgraph_builder.h"
#include "modular_fptr_analysis.h"
#include "modular_globals_analysis.h"

/*******************************************************************\

Function: collation

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void collation(std::istream &in, const optionst &options)
{
  cgraph_buildert cg_builder;
  modular_fptr_analysist fptr_analysis;
  modular_globals_analysist globals_analysis;
  
  cg_builder.add_analysis(&fptr_analysis);
  cg_builder.add_analysis(&globals_analysis);
  
  cg_builder.deserialize_list(in);
}
