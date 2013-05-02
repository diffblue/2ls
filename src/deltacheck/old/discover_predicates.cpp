/*******************************************************************\

Module: Predicate Discovery

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "discover_predicates.h"
#include "canonicalize.h"

/*******************************************************************\

Function: discover_predicates

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

#include <iostream>

std::list<exprt> discover_predicates(
  const exprt &src,
  const namespacet &ns)
{
  if(src.id()==ID_and || src.id()==ID_or)
  {
    std::list<exprt> result;

    forall_operands(it, src)
    {
      std::list<exprt> tmp=discover_predicates(*it, ns);
      result.insert(result.end(), tmp.begin(), tmp.end());
    }
    
    return result;
  }
  else if(src.id()==ID_not)
  {
    assert(src.operands().size()==1);
    return discover_predicates(src.op0(), ns);
  }
  else
  {
    exprt tmp=src;
    bool negation;
    canonicalize(tmp, negation, ns);
    std::list<exprt> result;
    result.push_back(tmp);
    return result;
  }  
}
