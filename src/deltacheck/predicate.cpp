/*******************************************************************\

Module: Delta Checking Solver

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "predicate.h"

/*******************************************************************\

Function: predicatet::get

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void predicatet::get(const solvert &solver)
{
}
  
/*******************************************************************\

Function: predicatet::set_to_true

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void predicatet::set_to_true(solvert &solver) const
{
}

/*******************************************************************\

Function: solvert::predicatet::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void predicatet::output(std::ostream &out) const
{
}

/*******************************************************************\

Function: predicatet::disjunction

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool predicatet::disjunction(const predicatet &other)
{
  return false;
}

/*******************************************************************\

Function: predicatet::rename

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void predicatet::rename(
  const symbol_exprt &new_guard,
  const var_listt &new_var_list)
{
}

