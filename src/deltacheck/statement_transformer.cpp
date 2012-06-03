/*******************************************************************\

Module: Summarization

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <simplify_expr.h>

#include <langapi/language_util.h>

#include <goto-programs/wp.h>

#include "canonicalize.h"
#include "statement_transformer.h"

/*******************************************************************\

Function: statement_transformert::assign

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

#include <iostream>

BDD statement_transformert::assign(
  const BDD &from,
  const code_assignt &assignment)
{
  BDD result=from;
  
  std::cout << "Statement: " << from_expr(ns, "", assignment.lhs())
            << " = " << from_expr(ns, "", assignment.rhs()) << std::endl;

  // Assign all predicates based on WP.
  // This is cheap cartesian abstraction.
  for(unsigned p=0; p<predicates.size(); p++)
  {
    std::cout << "P: " << predicates[p].string << std::endl;
    exprt wp=::wp(assignment, predicates[p].expr, ns);
    simplify(wp, ns);

    std::cout << "WP: " << from_expr(ns, "", wp) << std::endl;

    // abstract
    BDD wp_bdd=abstract(wp);
    result&=wp_bdd;
  }

  BDD old_var_cube=mgr.bddOne();
  
  // quantify away 'current', leaving 'next'
  result.ExistAbstract(old_var_cube);

  // swap 'next' and 'current'
  int *permutation=new int[mgr.ReadSize()];
  
  for(int i=0; i<mgr.ReadSize(); i++)
  {
    permutation[i]=i;

    if(i<(int)predicates.size()*2)
    {
      if(i%2==0)
        permutation[i]=i+1;
      else
        permutation[i]=i-1;
    }
  }
    
  result=result.Permute(permutation);
  
  delete permutation;
  
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
  else if(src.is_true())
  {
    return mgr.bddOne();
  }
  else if(src.is_false())
  {
    return !mgr.bddOne();
  }
  
  // canonicalize
  exprt tmp=src;
  bool negation;
  canonicalize(tmp, negation, ns);

  // check if 'tmp' is a predicate
  predicatest::predicate_mapt::const_iterator p_it=
    predicates.predicate_map.find(tmp);
  
  if(p_it!=predicates.predicate_map.end())
  {
    BDD result=predicates[p_it->second].var;
    if(negation) result=!result;
    return result;
  }

  // give up, produce non-determinism
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
  if(aux_variable_start==aux_variable_end) return src;

  // build cube made of auxiliary variables
  BDD cube=mgr.bddOne();
  
  for(unsigned i=aux_variable_start; i<aux_variable_end; i++)
    cube&=mgr.bddVar(i);

  // forget the auxiliary variables    
  aux_variable_end=aux_variable_start;
  
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
