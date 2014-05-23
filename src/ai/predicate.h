#ifndef CPROVER_DELTACHECK_PREDICATE_H
#define CPROVER_DELTACHECK_PREDICATE_H

#include <util/std_expr.h>

class predicatet : public predicate_exprt 
{
 public:
 predicatet() : predicate_exprt() {}
  predicatet(const exprt &_expr) : predicate_exprt(_expr.id(),_expr) 
  {
    assert(_expr.type().id()==ID_bool);
  }
};

#endif
