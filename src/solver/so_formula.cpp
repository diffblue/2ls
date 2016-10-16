/*******************************************************************\

Module: Second-Order Formula

Author: Peter Schrammel

\*******************************************************************/

#include "so_formula.h"


/*******************************************************************\

Function: so_formulat::is_well_formed()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool so_formulat::is_well_formed()
{
  //TODO
  return true;
} 

/*******************************************************************\

Function: so_formulat::bound_predicates()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void so_formulat::bound_predicates_rec(
  const exprt& expr, 
  predicate_symbol_sett& s)
{
  if(expr.id()==ID_exists)
  {
#if 0 //use this once fixed in util/std_expr
    const exists_exprt &e=to_exists_expr(e);
    s.insert(to_predicate_symbol_expr(e.symbol()));
    bound_predicates_rec(e.where(),s);
#else
    s.insert(to_predicate_symbol_expr(expr.op0()));
    bound_predicates_rec(expr.op1(),s);
#endif
  }
} 

predicate_symbol_sett so_formulat::bound_predicates()
{
  predicate_symbol_sett s;
  bound_predicates_rec(*this, s);
  return s;
} 

/*******************************************************************\

Function: so_formulat::free_predicates()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void so_formulat::free_predicates_rec(
  const exprt& expr, 
  const predicate_symbol_sett &bound_predicates,
  predicate_symbol_sett& s)
{
  if(expr.id()==ID_function_application)
  {
    const predicate_symbol_exprt &p=
      to_predicate_application_expr(expr).predicate();
    if(bound_predicates.find(p)==bound_predicates.end())
      s.insert(p);
  }
  else
    forall_operands(it, expr)
      free_predicates_rec(*it,bound_predicates,s);
} 

predicate_symbol_sett so_formulat::free_predicates(
  const predicate_symbol_sett &bound_predicates)
{
  predicate_symbol_sett s;
  free_predicates_rec(*this, bound_predicates, s);
  return s;
} 
