/*******************************************************************\

Module: Definition Domain

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

//#define DEBUG

#ifdef DEBUG
#include <iostream>
#endif

#include "guard_domain.h"

/*******************************************************************\

Function: guard_domaint::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void guard_domaint::output(
  const namespacet &ns,
  std::ostream &out) const
{
  for(guardst::const_iterator
      g_it=guards.begin();
      g_it!=guards.end();
      g_it++)
  {
    if(g_it!=guards.begin()) out << " ";
    if(!g_it->truth) out << "!";
    out << g_it->branch->location_number;
  }
  out << "\n";
}

/*******************************************************************\

Function: guard_domaint::transform

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void guard_domaint::transform(
  const namespacet &ns,
  locationt from,
  locationt to)
{
  if(from->is_goto())
  {
    if(from->get_target()==to)
    {
      // taken
      guards.push_back(guardt(from, true));
    }
    else
    {
      // not taken
      guards.push_back(guardt(from, false));
    }
  }
  else if(from->is_assume())
  {
    guards.push_back(guardt(from));
  }
}

/*******************************************************************\

Function: guard_domaint::merge

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool guard_domaint::merge(
  const guard_domaint &b,
  locationt to)
{
  bool result=false;

  // This is the 'OR' between the two conjunctions.
  // If this is something simple, we use it.
  // Otherwise, we introduce a brand-new guard.

  guards.clear();
  guards.push_back(guardt(to));
  
  return result;
}
