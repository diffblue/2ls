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

solvert::solvert(const namespacet &_ns):decision_proceduret(_ns)
{
  false_nr=add(false_exprt());
  true_nr=add(true_exprt());
}

/*******************************************************************\

Function: solvert::add

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void solvert::add(unsigned nr)
{
  const exprt &expr=expr_numbering[nr];
    
  if(expr.id()==ID_if)
  {
    const if_exprt &if_expr=to_if_expr(expr);

    // the three calls below are possibly recursive,
    // and thus, "if_list" isn't stable
    solver_ift solver_if;
    solver_if.cond=add(if_expr.cond());
    solver_if.true_case=add(if_expr.true_case());
    solver_if.false_case=add(if_expr.false_case());
    solver_if.e_nr=nr;

    if_list.push_back(solver_if);
  }
}

/*******************************************************************\

Function: solvert::dec_solve

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

decision_proceduret::resultt solvert::dec_solve()
{
  bool progress;
  
  do
  {  
    progress=false;

    for(if_listt::const_iterator
        if_it=if_list.begin();
        if_it!=if_list.end();
        if_it++)
    {
      if(is_equal(if_it->cond, false_nr)) // false ? x : y == y
      {
        if(!is_equal(if_it->false_case, if_it->e_nr))
        {
          set_equal(if_it->false_case, if_it->e_nr);
          progress=true;
        }
      }
      else if(is_equal(if_it->cond, true_nr)) // true ? x : y == x
      {
        if(!is_equal(if_it->true_case, if_it->e_nr))
        {
          set_equal(if_it->true_case, if_it->e_nr);
          progress=true;
        }
      }

      // c ? x : x == x
      if(is_equal(if_it->false_case, if_it->true_case) &&
         !is_equal(if_it->false_case, if_it->e_nr))
      {
        set_equal(if_it->false_case, if_it->e_nr);
        progress=true;
      }
    }
  }
  while(progress);

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
  else
  {
    set_equal(add(expr), value?true_nr:false_nr);
  }
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
  
