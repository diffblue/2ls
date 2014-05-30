/*******************************************************************\

Module: Discover the Guards of Basic Blocks

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_GUARD_MAP_H
#define CPROVER_GUARD_MAP_H

#include <ostream>
#include <cassert>
#include <map>

#include <goto-programs/goto_program.h>

class guard_mapt
{
public:
  inline explicit guard_mapt(const goto_programt &src)
  {
    build(src);
  }
  
  typedef goto_programt::const_targett locationt;    

  struct edget
  {
    locationt from, guard_source;
    exprt guard;
    inline edget(locationt f, exprt g):from(f), guard(g)
    {
    }
  };

  typedef std::list<edget> incomingt;

  struct entryt
  {
  public:
    inline entryt():has_guard(false) { }
    bool has_guard;
    
    // if location has a guard of its own this is a self-pointer
    locationt guard_source;
    
    // if it has a guard of its own:
    incomingt incoming;

    inline void add_in(locationt l, exprt g)
    {
      has_guard=true;
      incoming.push_back(edget(l, g));
    }
  };
  
  // Query me! I return the entry for any program location.
  inline const entryt &operator[](const locationt location) const
  {
    mapt::const_iterator it=map.find(location);
    assert(it!=map.end());
    return it->second;
  }
  
  void output(
    const goto_programt &goto_program,
    std::ostream &) const;
  
protected:
  void build(const goto_programt &src);
  
  typedef std::map<locationt, entryt> mapt;
  mapt map;
};

#endif
