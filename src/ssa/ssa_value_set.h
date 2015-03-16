/*******************************************************************\

Module: A flow-insensitive value set analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SSA_VALUE_SET_H
#define CPROVER_SSA_VALUE_SET_H

#include <goto-programs/goto_functions.h>

#include "ssa_object.h"

class ssa_value_sett
{
public:
  const ssa_objectst &ssa_objects;

  typedef ssa_objectt::identifiert identifiert;

  // maps object identifiers to their values,
  // which are sets of object identifiers
  typedef std::map<identifiert, std::set<identifiert> > value_mapt;
  value_mapt value_map;
  
  #if 0
  bool assigns(goto_programt::const_targett loc, const ssa_objectt &object) const
  {
    assignment_mapt::const_iterator it=assignment_map.find(loc);
    if(it==assignment_map.end()) return false;
    return it->second.find(object)!=it->second.end();
  }
  
  inline const objectst &get(goto_programt::const_targett loc) const
  {
    assignment_mapt::const_iterator it=assignment_map.find(loc);
    assert(it!=assignment_map.end());
    return it->second;
  }

  explicit assignmentst(
    const goto_programt &_goto_program,
    const namespacet &_ns,
    const ssa_objectst &_ssa_objects):
    ssa_objects(_ssa_objects)
  {
    build_assignment_map(_goto_program, _ns);
  }
  #endif
  
  void output(
    const namespacet &ns,
    const goto_programt &_goto_program,
    std::ostream &);
  
protected:
  #if 0
  void build_assignment_map(const goto_programt &, const namespacet &);

  void assign(
    const exprt &lhs, goto_programt::const_targett,
    const namespacet &ns);
    
  void assign(
    const ssa_objectt &lhs, goto_programt::const_targett,
    const namespacet &ns);    
  #endif
};

#endif
