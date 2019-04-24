/*******************************************************************\

Module: Discover the Guards of Basic Blocks

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Discover the Guards of Basic Blocks

#include <util/expr_util.h>

#include "guard_map.h"

void guard_mapt::output(
  const goto_programt &src,
  std::ostream &out) const
{
  forall_goto_program_instructions(it, src)
  {
    const entryt &entry=operator[](it);
    out << "*** " << it->location_number
        << " guard " << entry.guard_source->location_number
        << ", in:";

    for(incomingt::const_iterator in_it=entry.incoming.begin();
        in_it!=entry.incoming.end();
        in_it++)
      out << " " << in_it->guard_source->location_number
          << " (" << in_it->kind << ")";

    out << "\n";
  }
}

void guard_mapt::build(const goto_programt &src)
{
  // first get all branch targets

  forall_goto_program_instructions(it, src)
  {
    locationt next=it;
    next++;

    if(it->is_goto())
    {
      map[it->get_target()->location_number].add_in(it, TAKEN);

      if(!it->guard.is_true())
        map[next->location_number].add_in(it, NOT_TAKEN);
      else
        map[next->location_number].has_guard=true;
    }
    else if(it->is_assume())
    {
      // these are much like gotos to a sink location
      map[next->location_number].add_in(it, ASSUME);
    }
    else if(it->is_function_call())
    {
      // functions might not return
      map[next->location_number].add_in(it, FUNCTION_CALL);
    }
  }

  // Also make the function entry location have a guard
  if(!src.instructions.empty())
    map[src.instructions.begin()->location_number].has_guard=true;

  // now assign the guard sources accordingly

  locationt g;

  forall_goto_program_instructions(it, src)
  {
    entryt &entry=map[it->location_number];

    if(entry.has_guard)
    {
      entry.guard_source=it; // self-pointer
      g=it;
    }
    else
      entry.guard_source=g; // previous
  }

  // Locations with guards get the successor edge
  // in the CFG.

  locationt previous;

  forall_goto_program_instructions(it, src)
  {
    // skip first, which has no predecessor
    if(it!=src.instructions.begin())
    {
      entryt &entry=map[it->location_number];

      // no need if previous is a goto
      if(entry.has_guard &&
         !previous->is_goto() &&
         !previous->is_assume() &&
         !previous->is_function_call())
        entry.add_in(previous, SUCCESSOR);
    }

    previous=it;
  }

  // now do guard sources of edges

  for(mapt::iterator m_it=map.begin(); m_it!=map.end(); m_it++)
  {
    for(incomingt::iterator i_it=m_it->second.incoming.begin();
        i_it!=m_it->second.incoming.end();
        i_it++)
    {
      i_it->guard_source=operator[](i_it->from).guard_source;
    }
  }
}
