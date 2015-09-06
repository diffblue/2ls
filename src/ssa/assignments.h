/*******************************************************************\

Module: A map of program locations to the assignments made there

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_ASSIGNMENTS_H
#define CPROVER_ASSIGNMENTS_H

#include <goto-programs/goto_functions.h>

#include "ssa_object.h"
#include "ssa_value_set.h"

class assignmentst
{
public:
  typedef goto_programt::const_targett locationt;

  const ssa_objectst &ssa_objects;
  const ssa_value_ait &ssa_value_ai;

  typedef ssa_objectst::objectst objectst;

  typedef std::map<locationt, objectst> assignment_mapt;
  assignment_mapt assignment_map;
  
  bool assigns(locationt loc, const ssa_objectt &object) const
  {
    assignment_mapt::const_iterator it=assignment_map.find(loc);
    if(it==assignment_map.end()) return false;
    return it->second.find(object)!=it->second.end();
  }
  
  inline const objectst &get(locationt loc) const
  {
    assignment_mapt::const_iterator it=assignment_map.find(loc);
    assert(it!=assignment_map.end());
    return it->second;
  }

  explicit assignmentst(
    const goto_programt &_goto_program,
    const namespacet &_ns,
    const ssa_objectst &_ssa_objects,
    const ssa_value_ait &_ssa_value_ai):
    ssa_objects(_ssa_objects),
    ssa_value_ai(_ssa_value_ai)
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
    const exprt &lhs, locationt,
    const namespacet &ns);
    
  void assign(
    const ssa_objectt &lhs, locationt,
    const namespacet &ns);    
};

#endif
