/*******************************************************************\

Module: Discover the Guards of Basic Blocks

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/expr_util.h>

#include "guard_map.h"

/*******************************************************************\

Function: guard_mapt::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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
      out << " " << in_it->guard_source->location_number;
        
    out << "\n";
  }
}

/*******************************************************************\

Function: guard_mapt::build

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void guard_mapt::build(const goto_programt &src)
{
  // first get all branch targets

  forall_goto_program_instructions(it, src)
  {
    locationt next=it;
    next++;
  
    if(it->is_goto())
    {
      map[it->get_target()].add_in(it, it->guard);  
      map[next].add_in(it, boolean_negate(it->guard));
    }
    else if(it->is_assume())
    {
      // these are much like gotos to a sink location
      map[next].add_in(it, it->guard);
    }
  }

  // The following nodes get a guard:
  // 1) everything that's a branch target
  // 2) the entry location
  // 3) successors of assumptions

  forall_goto_program_instructions(it, src)
  {
    entryt &entry=map[it];
  
    if(it==src.instructions.begin() ||
       !entry.incoming.empty())
      entry.has_guard=true;
  }
  
  // now assign the guard sources accordingly

  locationt g;

  forall_goto_program_instructions(it, src)
  {
    entryt &entry=map[it];
    
    if(entry.has_guard)
    {
      entry.guard_source=it;
      g=it;
    }
    else
      entry.guard_source=g;
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
