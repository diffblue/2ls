/*******************************************************************\

Module: Definition Analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_ASSIGNMENTS_H
#define CPROVER_ASSIGNMENTS_H

#include <goto-programs/goto_program.h>

#include "ssa_object.h"

class assignmentst
{
public:
  typedef std::set<ssa_objectt> objectst;
  objectst objects;
  
  typedef std::map<goto_programt::const_targett, objectst> assignment_mapt;
  assignment_mapt assignment_map;
  
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
    const namespacet &_ns)
  {
    build(_goto_program, _ns);
  }
  
  static bool may_alias(const ssa_objectt &, const ssa_objectt &);

protected:
  void build(const goto_programt &, const namespacet &);

  void assign(
    const exprt &lhs, goto_programt::const_targett,
    const namespacet &ns);
    
  void assign(
    const ssa_objectt &lhs, goto_programt::const_targett,
    const namespacet &ns);    
};

#endif
