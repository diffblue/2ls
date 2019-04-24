/*******************************************************************\

Module: Discover the Guards of Basic Blocks

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Discover the Guards of Basic Blocks

#ifndef CPROVER_2LS_SSA_GUARD_MAP_H
#define CPROVER_2LS_SSA_GUARD_MAP_H

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

  enum kindt { SUCCESSOR, TAKEN, NOT_TAKEN, ASSUME, FUNCTION_CALL } kind;

  friend std::ostream & operator << (std::ostream &out, kindt kind)
  {
    switch(kind)
    {
    case SUCCESSOR: return out << "SUC";
    case TAKEN: return out << "BTK";
    case NOT_TAKEN: return out << "BNT";
    case ASSUME: return out << "ASS";
    case FUNCTION_CALL: return out << "FKT";
    default: return out << "?";
    }
  }

  struct edget
  {
    locationt from, guard_source;
    kindt kind;

    bool is_branch_not_taken() const
    {
      return kind==NOT_TAKEN;
    }

    bool is_branch_taken() const
    {
      return kind==TAKEN;
    }

    bool is_assume() const
    {
      return kind==ASSUME;
    }

    bool is_successor() const
    {
      return kind==SUCCESSOR;
    }

    bool is_function_call() const
    {
      return kind==FUNCTION_CALL;
    }

    inline edget(locationt f, kindt k):from(f), kind(k)
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

    inline void add_in(locationt l, kindt k)
    {
      has_guard=true;
      incoming.push_back(edget(l, k));
    }
  };

  // Query me! I return the entry for any program location.
  inline const entryt &operator[](const locationt location) const
  {
    mapt::const_iterator it=map.find(location->location_number);
    assert(it!=map.end());
    return it->second;
  }

  void output(
    const goto_programt &goto_program,
    std::ostream &) const;

protected:
  void build(const goto_programt &src);

  // use location number as key to make iteration deterministic
  typedef std::map<unsigned, entryt> mapt;
  mapt map;
};

#endif
