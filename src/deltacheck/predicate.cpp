/*******************************************************************\

Module: Delta Checking Solver

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <langapi/language_util.h>

#include "predicate.h"

/*******************************************************************\

Function: predicatet::get

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void predicatet::get(const solvert &solver)
{
  // first get guard, conservatively
  if(solver.get(guard).is_false())
  {
    is_false=true;
    uuf.clear();
    return;
  }
  else
    is_false=false;

  // Get equalities from solver.
  // Could do linear instead of quadratic.
  for(unsigned v1=0; v1<vars.size(); v1++)
    for(unsigned v2=v1+1; v2<vars.size(); v2++)
      if(solver.is_equal(vars[v1], vars[v2]))
        uuf.make_union(v1, v2);
}
  
/*******************************************************************\

Function: predicatet::set_to_true

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void predicatet::set_to_true(solvert &solver) const
{
  if(is_false)
  {
    solver.set_to_false(guard);
  }
  else
  {
    // pass equalities to solver
    
    for(unsigned v=0; v<vars.size(); v++)
    {
      unsigned eq=uuf.find(v);
      if(eq!=v) solver.set_equal(vars[v], vars[eq]);
    }
  }
}

/*******************************************************************\

Function: solvert::predicatet::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void predicatet::output(std::ostream &out) const
{
  if(is_false)
  {
    out << "FALSE" << "\n";
    return;
  }
  else
  {
    // print equalities in pretty way
    
    std::map<unsigned, unsigned> eq_count;
    
    for(unsigned v=0; v<vars.size(); v++)
      eq_count[uuf.find(v)]++;

    for(std::map<unsigned, unsigned>::const_iterator
        e_it=eq_count.begin(); e_it!=eq_count.end(); e_it++)
    {
      if(e_it->second>=2)
      {
        for(unsigned v=0; v<vars.size(); v++)
          if(e_it->first==uuf.find(v))
            out << "Equal: " << from_expr(vars[v]) << "\n";
        out << "\n";
      }
    }
    
    // print intervals
    for(intervalst::const_iterator
        i_it=intervals.begin(); i_it!=intervals.end(); i_it++)
    {
      if(i_it->lower_is_set || i_it->upper_is_set)
      {
        if(i_it->lower_is_set)
          out << from_expr(i_it->lower) << " <= ";
          
        out << from_expr(vars[i_it-intervals.begin()]);
          
        if(i_it->upper_is_set)
          out << " <= " << from_expr(i_it->lower);
          
        out << "\n";
      }
    }
  }
}

/*******************************************************************\

Function: predicatet::disjunction

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool predicatet::disjunction(const predicatet &other)
{
  if(is_false && other.is_false) return false;

  if(is_false && !other.is_false)
  {
    *this=other;
    return true;
  }

  return false;
}

/*******************************************************************\

Function: predicatet::rename

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void predicatet::rename(
  const symbol_exprt &new_guard,
  const var_listt &new_vars)
{
  assert(vars.size()==new_vars.size());

  guard=new_guard;
  vars=new_vars;
}

