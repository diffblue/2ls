/*******************************************************************\

Module: Delta Checking Abstract State

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

void predicatet::make_false()
{
  uuf.resize(state_vars.size());

  for(unsigned v1=0; v1<state_vars.size(); v1++)
    for(unsigned v2=0; v2<state_vars.size(); v2++)
      if(state_vars[v1].type()==state_vars[v2].type())
        uuf.make_union(v1, v2);
}

/*******************************************************************\

Function: predicatet::get

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

#if 0
void predicatet::get(const solvert &solver)
{
  // Get equalities from solver.
  // Could do linear instead of quadratic, exploiting the
  // data structure.
  for(unsigned v1=0; v1<state_vars.size(); v1++)
    for(unsigned v2=v1+1; v2<state_vars.size(); v2++)
      if(solver.is_equal(state_vars[v1], state_vars[v2]))
        uuf.make_union(v1, v2);
}
#endif
  
/*******************************************************************\

Function: predicatet::set_to_true

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void predicatet::set_to_true(decision_proceduret &dest) const
{
  // pass equalities to solver
    
  for(unsigned v=0; v<state_vars.size(); v++)
  {
    unsigned eq=uuf.find(v);
    if(eq!=v) dest.set_to_true(equal_exprt(state_vars[v], state_vars[eq]));
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
  // print equalities in pretty way
  
  out << "State vars:";
  for(unsigned v=0; v<state_vars.size(); v++)
    out << " " << from_expr(state_vars[v]);
  out << "\n";
  
  std::map<unsigned, unsigned> eq_count;
  
  for(unsigned v=0; v<state_vars.size(); v++)
    eq_count[uuf.find(v)]++;

  for(std::map<unsigned, unsigned>::const_iterator
      e_it=eq_count.begin(); e_it!=eq_count.end(); e_it++)
  {
    if(e_it->second>=2)
    {
      for(unsigned v=0; v<state_vars.size(); v++)
        if(e_it->first==uuf.find(v))
          out << "Equal: " << from_expr(state_vars[v]) << "\n";
      out << "\n";
    }
  }
  
  // print intervals
  #if 0
  for(integer_intervalst::const_iterator
      i_it=integer_intervals.begin(); i_it!=integer_intervals.end(); i_it++)
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
  #endif
}

/*******************************************************************\

Function: predicatet::disjunction

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool predicatet::disjunction(const predicatet &other)
{
  bool change=false;

  //
  // do equalities
  //

  assert(other.state_vars.size()==state_vars.size());

  unsigned_union_find new_uuf;
  new_uuf.resize(uuf.size());

  // can be done better than quadratic
  for(unsigned v1=0; v1<state_vars.size(); v1++)
    for(unsigned v2=0; v2<state_vars.size(); v2++)
      if(v1!=v2 && uuf.same_set(v1, v2))
      {
        if(other.uuf.same_set(v1, v2)) // same true in 'other'?
          new_uuf.make_union(v1, v2);
        else
          change=true; // things got weaker
      }
  
  assert(uuf.size()==new_uuf.size());
  uuf.swap(new_uuf);

  return change;
}

/*******************************************************************\

Function: predicatet::rename

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void predicatet::rename(const state_var_listt &new_state_vars)
{
  // We can't change the size of the support set,
  // only the names of the variables.
  assert(state_vars.size()==new_state_vars.size());

  state_vars=new_state_vars;
}

