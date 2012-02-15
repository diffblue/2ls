/*******************************************************************\

Module: Collation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "collation.h"
#include "cgraph_builder.h"
#include "modular_fptr_analysis.h"

/*******************************************************************\

Function: collation

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void collation(std::istream &in, const optionst &options)
{
  cgraph_buildert cg_builder;
  
  cg_builder.add_analysis(new modular_fptr_analysist());
  
  cg_builder.deserialize_list(in);
}
