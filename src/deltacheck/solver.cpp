/*******************************************************************\

Module: Delta Checking Solver

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/expr.h>
#include <util/std_expr.h>

#include "solver.h"

/*******************************************************************\

Function: solvert::set_to

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void solvert::set_to(const exprt &expr, bool value)
{
  if(expr.id()==ID_equal)
  {
    if(value)
      set_equal(to_equal_expr(expr).lhs(), to_equal_expr(expr).rhs());
  }
  else if(expr.id()==ID_notequal)
  {
    if(!value)
      set_equal(to_notequal_expr(expr).lhs(), to_notequal_expr(expr).rhs());
  }
}
  
/*******************************************************************\

Function: solvert::set_equal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void solvert::set_equal(const exprt &lhs, const exprt &rhs)
{
}
  
/*******************************************************************\

Function: solvert::get

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt solvert::get(const exprt &expr) const
{
  return nil_exprt();
}
  
/*******************************************************************\

Function: solvert::print_assignment

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void solvert::print_assignment(std::ostream &out) const
{
}
  
/*******************************************************************\

Function: solvert::join

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool solvert::join(const src_listt &src,
                   const var_sett &dest)
{
  return false;
}
  
