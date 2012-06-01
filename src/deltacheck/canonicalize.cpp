/*******************************************************************\

Module: Partial Canonicalization of a Predicate

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <simplify_expr.h>
#include <expr.h>
#include <namespace.h>

#include "canonicalize.h"

/*******************************************************************\

Function: canonicalize_rec

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void canonicalize_rec(exprt &expr, bool &negation)
{
  if(expr.id()==ID_not)
  {
    if(expr.operands().size()==1)
    {
      exprt tmp;
      tmp.swap(expr.op0());
      negation=!negation;
      canonicalize_rec(tmp, negation);
      expr.swap(tmp);
    }
  }
  else if(expr.id()==ID_notequal)
  {
    if(expr.operands().size()==2)
    {
      negation=!negation;
      expr.id(ID_equal);
      canonicalize_rec(expr, negation);
    }
  } 
  else if(expr.id()==ID_ge) // we only use le and lt
  {
    if(expr.operands().size()==2)
    {
      negation=!negation;
      expr.id(ID_lt);
      canonicalize_rec(expr, negation);
    }
  } 
  else if(expr.id()==ID_gt) // we only use le and lt
  {
    if(expr.operands().size()==2)
    {
      negation=!negation;
      expr.id(ID_le);
      canonicalize_rec(expr, negation);
    }
  } 
  else if(expr.id()==ID_le || expr.id()==ID_lt)
  {
    if(expr.operands().size()==2)
    {

    }
  } 
  else if(expr.id()==ID_equal)
  {
    // we order the operands with <
    assert(expr.operands().size()==2);

    if(expr.op0()<expr.op1())
    {
    }
    else
      expr.op0().swap(expr.op1());
  }
}

/*******************************************************************\

Function: clean_annotations_and_type_rec

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void clean_annotations_and_type_rec(exprt &expr, const namespacet &ns)
{
  expr.remove(ID_C_cformat);
  expr.remove(ID_C_location);

  if(expr.type().id()==ID_symbol)
  {
    typet type=ns.follow(expr.type());
    expr.type().swap(type);
  }

  Forall_operands(it, expr)
    clean_annotations_and_type_rec(*it, ns);
}

/*******************************************************************\

Function: canonicalize

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void canonicalize(exprt &expr, bool &negation, const namespacet &ns)
{
  // we expect an expression of type Boolean
  if(expr.type().id()!=ID_bool)
    throw "canonicalize expects expression of Boolean type";

  simplify(expr, ns);

  negation=false;

  canonicalize_rec(expr, negation);

  clean_annotations_and_type_rec(expr, ns);
}

/*******************************************************************\

Function: canonicalize

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void canonicalize(exprt &expr, const namespacet &ns)
{
  bool negation;

  canonicalize(expr, negation, ns);

  if(negation) expr.make_not();
}

