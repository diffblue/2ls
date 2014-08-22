/*******************************************************************\

Module: Summarization

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <langapi/language_util.h>

#include "predicates.h"

/*******************************************************************\

Function: predicatest::make_list

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string predicatest::make_list() const
{
  std::string result;

  for(predicate_vectort::const_iterator
      p_it=predicate_vector.begin();
      p_it!=predicate_vector.end();
      p_it++)
  {
    if(p_it!=predicate_vector.begin()) result+=", ";
    result+=from_expr(ns, "", p_it->expr);
  }
  
  return result;
}

/*******************************************************************\

Function: predicatest::add

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void predicatest::add(Cudd &mgr, const exprt &src)
{
  if(predicate_map.find(src)!=predicate_map.end())
    return;

  unsigned index=size();

  predicate_vector.push_back(predicatet());
  predicate_vector.back().expr=src;
  
  // this will cause the ordering of the variable and
  // it's next-state version to be interleaved
  predicate_vector.back().var=mgr.bddVar(index*2);
  predicate_vector.back().next_var=mgr.bddVar(index*2+1);
  predicate_vector.back().string=from_expr(ns, "", src);
  
  predicate_map[src]=index;
}
