/*******************************************************************\

Module: Summarization

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <simplify_expr.h>

#include <goto-programs/wp.h>

#include "statement_transformer.h"

/*******************************************************************\

Function: statement_transformert::assign

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

BDD statement_transformert::assign(
  const BDD &from,
  const code_assignt &assignment)
{
  BDD result=from;

  // assign all predicates based on WP
  for(unsigned p=0; p<predicates.size(); p++)
  {
    exprt wp=::wp(assignment, predicates[p].expr, ns);
    simplify(wp, ns);
    //result
  }

  BDD old_var_cube=mgr.bddOne();
  
  // quantify away 'current'
  result.ExistAbstract(old_var_cube);
  
  // rename 'next' back to 'current'
  
  return result;
}

/*******************************************************************\

Function: statement_transformert::abstract

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

BDD statement_transformert::abstract(const exprt &src)
{
  // boolean structure
  
  if(src.id()==ID_or)
  {
    BDD result=!mgr.bddOne();

    forall_operands(it, src)
      result|=abstract(*it);

    return result;
  }
  else if(src.id()==ID_and)
  {
    BDD result=mgr.bddOne();

    forall_operands(it, src)
      result&=abstract(*it);

    return result;
  }
  else if(src.id()==ID_not)
  {
    assert(src.operands().size()==1);
    return !abstract(src.op0());
  }

  // check if 'src' is a predicate
  return aux_variable();
}

/*******************************************************************\

Function: statement_transformert::remove_aux

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

BDD statement_transformert::remove_aux(const BDD &src)
{
  BDD cube=mgr.bddOne();
  
  for(unsigned i=aux_variable_start; i<aux_variable_end; i++)
    cube&=mgr.bddVar(i);
  
  return src.ExistAbstract(cube);
}

/*******************************************************************\

Function: statement_transformert::aux_variable

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

BDD statement_transformert::aux_variable()
{
  if(aux_variable_start!=predicates.size()*2)
  {
    // first use
    aux_variable_end=aux_variable_start=predicates.size()*2;
  }
  
  return mgr.bddVar(aux_variable_end++);
}
