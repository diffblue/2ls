/*******************************************************************\

Module: A map of program locations to the assignments made there

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// A map of program locations to the assignments made there

#ifndef CPROVER_2LS_SSA_ASSIGNMENTS_H
#define CPROVER_2LS_SSA_ASSIGNMENTS_H

#include <goto-programs/goto_functions.h>

#include "ssa_object.h"
#include "ssa_value_set.h"

class assignmentst
{
public:
  typedef goto_programt::const_targett locationt;

  const ssa_objectst &ssa_objects;
  const ssa_value_ait &ssa_value_ai;
  const ssa_heap_analysist &ssa_heap_analysis;

  typedef ssa_objectst::objectst objectst;

  typedef std::map<locationt, objectst> assignment_mapt;
  assignment_mapt assignment_map;

  typedef std::map<std::pair<locationt, ssa_objectt>, exprt> alloc_guards_mapt;
  alloc_guards_mapt alloc_guards_map;

  bool assigns(locationt loc, const ssa_objectt &object) const
  {
    assignment_mapt::const_iterator it=assignment_map.find(loc);
    if(it==assignment_map.end())
      return false;
    return it->second.find(object)!=it->second.end();
  }

  inline const objectst &get(locationt loc) const
  {
    assignment_mapt::const_iterator it=assignment_map.find(loc);
    assert(it!=assignment_map.end());
    return it->second;
  }

  assignmentst(
    const goto_programt &_goto_program,
    const namespacet &_ns,
    const ssa_objectst &_ssa_objects,
    const ssa_value_ait &_ssa_value_ai,
    const ssa_heap_analysist &_ssa_heap_analysis):
    ssa_objects(_ssa_objects),
    ssa_value_ai(_ssa_value_ai),
    ssa_heap_analysis(_ssa_heap_analysis)
  {
    build_assignment_map(_goto_program, _ns);
  }

  void output(
    const namespacet &ns,
    const goto_programt &_goto_program,
    std::ostream &);

protected:
  void build_assignment_map(const goto_programt &, const namespacet &);

  void assign(
    const exprt &lhs,
    locationt,
    const namespacet &ns);

  void assign(
    const ssa_objectt &lhs,
    locationt,
    const namespacet &ns);

  void assign_symbolic_rhs(
    const exprt &expr,
    const locationt &loc,
    const namespacet &ns);

  void create_alloc_decl(
    const exprt &expr,
    const exprt &guard,
    const locationt loc,
    const namespacet &ns);
};

#endif
