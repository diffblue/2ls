/*******************************************************************\

Module: SSA Objects

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SSA_OBJECTS_H
#define CPROVER_SSA_OBJECTS_H

#include "object_id.h"

class ssa_objectt
{
public:
  inline explicit ssa_objectt(const exprt &_expr):
    expr(_expr),
    identifier(object_id(expr))
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

protected:
  exprt expr;
  irep_idt identifier;
};

#endif
