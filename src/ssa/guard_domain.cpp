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
  std::ostream &out,
  const ai_baset &,
  const namespacet &ns) const
{
  if(unreachable)
  {
    out << "UNREACHABLE\n";
    return;
  }

  for(guardst::const_iterator
      g_it=guards.begin();
      g_it!=guards.end();
      g_it++)
  {
    if(g_it!=guards.begin()) out << " ";
    switch(g_it->kind)
    {
    case guardt::NONE: assert(false); break;
    case guardt::BRANCH_TAKEN: out << "bt"; break;
    case guardt::BRANCH_NOT_TAKEN: out << "bnt"; break;
    case guardt::MERGED: break;
    }

    out << g_it->loc->location_number;
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
  locationt from,
  locationt to,
  ai_baset &,
  const namespacet &ns)
{
  if(unreachable) return;

  if(from->is_goto())
  {
    if(from->get_target()==to)
    {
      // taken
      if(!from->guard.is_true())
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
  else if(from->is_function_call())
  {
    // Functions might not return, but we will assume that
    // for now.
    //guards.push_back(guardt(from));
  }
}

/*******************************************************************\

Function: guard_domaint::merge

  Inputs:

 Outputs: return true if "this" has changed

 Purpose:

\*******************************************************************/

bool guard_domaint::merge(
  const guard_domaint &b,
  locationt from,
  locationt to)
{
  // Merging a blank state doesn't change anything.
  if(b.unreachable) return false;

  // update 'from'
  incoming[from]=b.guards;

  if(unreachable)
  {
    // copy guards of 'b'
    unreachable=false;
    guards=b.guards;
    return true;
  }
  
  guardst new_guards;
  
  // Just one incoming edge?
  if(incoming.size()==1)
  {
    new_guards=incoming.begin()->second;
  }
  else if(incoming.size()==2)
  {
    // This is the 'OR' between the two conjunctions.
    // If this is something simple, we use it.
    const guardst &g1=incoming.begin()->second;
    const guardst &g2=incoming.rbegin()->second;
  
    if(prefix_match(g1, g2) &&
       g1.back().is_branch() && g2.back().is_branch() &&
       g1.back().loc==g2.back().loc)
    {
      // We have PREFIX bt loc and PREFIX bnt loc.
      // The 'OR' is PREFIX.
      new_guards=g1;
      new_guards.resize(new_guards.size()-1);
    }
    else
    {
      // introduce merge guard
      new_guards.push_back(guardt(to));
    }
  }
  else
  {
    // Otherwise, we introduce a brand-new merge guard.
    new_guards.push_back(guardt(to));
  }
  
  if(new_guards==guards)
    return false;

  guards.swap(new_guards);
  
  return true;
}
