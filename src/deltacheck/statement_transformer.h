/*******************************************************************\

Module: Summarization

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cuddObj.hh>

#include <list>

#include <namespace.h>
#include <expr.h>
#include <std_code.h>

#include "predicates.h"

class statement_transformert
{
public:
  statement_transformert(
    const predicatest &_predicates,
    Cudd &_mgr,
    const namespacet &_ns):
    predicates(_predicates),
    mgr(_mgr),
    ns(_ns),
    aux_variable_start(0),
    aux_variable_end(0)
  {
  }

  BDD assign(
    const BDD &from, const code_assignt &assignment);

  inline BDD guard(const BDD &from, const exprt &g)
  {
    return remove_aux(from & abstract(g));
  }

  inline BDD guard_not(const BDD &from, const exprt &g)
  {
    return remove_aux(from & !abstract(g));
  }

protected:
  const predicatest &predicates;
  Cudd &mgr;
  const namespacet &ns;

  BDD abstract(const exprt &g);
  BDD remove_aux(const BDD &src);

  // record any auxiliary variables
  unsigned aux_variable_start, aux_variable_end;
  
  BDD aux_variable();
};
