/*******************************************************************\

Module: SSA Objects

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SSA_OBJECTS_H
#define CPROVER_SSA_OBJECTS_H

#include <goto-programs/goto_program.h>

class ssa_objectt
{
public:
  inline explicit ssa_objectt(const exprt &_expr):
    expr(_expr),
    identifier(object_id_rec(expr))
  {
  }
  
  inline const exprt &get_expr() const
  {
    return expr;
  }
  
  inline irep_idt get_identifier() const
  {
    return identifier;
  }
  
  inline bool operator<(const ssa_objectt &other) const
  {
    return identifier<other.identifier;
  }
  
  // this is for use in if(...) tests
  operator void *() const
  {
    return identifier.empty()?0:(void *)&identifier;
  }

protected:
  exprt expr;
  irep_idt identifier;

  static irep_idt object_id_rec(const exprt &src);
};

void collect_objects(
  const goto_programt &,
  const namespacet &,
  std::set<ssa_objectt> &);

#endif
