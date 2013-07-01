/*******************************************************************\

Module: Delta Checking Solver

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <map>
#include <set>

#include <langapi/language_util.h>

#include <util/expr.h>
#include <util/std_expr.h>

#include "solver.h"

/*******************************************************************\

Function: solvert::dec_solve

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

decision_proceduret::resultt solvert::dec_solve()
{
  return D_ERROR;
}

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
  // add to union find
  unsigned lhs_nr=expr_numbering(lhs),
           rhs_nr=expr_numbering(rhs);

  equalities.make_union(lhs_nr, rhs_nr);
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
  std::map<unsigned, std::set<unsigned> > equality_map;
  
  for(unsigned i=0; i<expr_numbering.size(); i++)
    equality_map[equalities.find(i)].insert(i);
  
  for(std::map<unsigned, std::set<unsigned> >::const_iterator
      e_it=equality_map.begin();
      e_it!=equality_map.end();
      e_it++)
  {
    const std::set<unsigned> &eq_set=e_it->second;
  
    if(eq_set.size()>=2)
    {
      for(std::set<unsigned>::const_iterator
          eq_it=eq_set.begin(); eq_it!=eq_set.end(); eq_it++)
      {
        out << "Equal: "
            << from_expr(ns, "", expr_numbering[*eq_it]) << std::endl;
      }

      out << std::endl;
    }
  }
}
  
/*******************************************************************\

Function: solvert::weaken

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void solvert::weaken(
  const var_listt &vars,
  predicatet &dest)
{
}
  
/*******************************************************************\

Function: solvert::assume

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void solvert::assume(
  const var_listt &vars,
  const predicatet &dest)
{
}

/*******************************************************************\

Function: solvert::predicatet::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void solvert::predicatet::output(std::ostream &out) const
{
}

