/*******************************************************************\

Module: Summary

Author: Peter Schrammel

\*******************************************************************/

#include "summary.h"
#include <langapi/language_util.h>

/*******************************************************************\

Function: summaryt::output()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summaryt::output(std::ostream &out, const namespacet &ns) const
{
  out << "params: ";
  for(summaryt::var_listt::const_iterator it = params.begin();
      it != params.end(); it++)
    out << from_expr(ns,"",*it) << " ";
  out << std::endl;
  out << "globals_in: ";
  for(summaryt::var_sett::const_iterator it = globals_in.begin();
      it != globals_in.end(); it++)
    out << from_expr(ns,"",*it) << " ";
  out << std::endl;
  out << "globals_out: ";
  for(summaryt::var_sett::const_iterator it = globals_out.begin();
      it != globals_out.end(); it++)
    out << from_expr(ns,"",*it) << " ";
  out << std::endl;
  out << "precondition: " << from_expr(ns,"",precondition) << std::endl;
  out << "transformer: " << from_expr(ns,"",transformer) << std::endl;
  out << "invariant: " << from_expr(ns,"",invariant) << std::endl;
}

/*******************************************************************\

Function: summaryt::join()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summaryt::combine_and(exprt &olde, const exprt &newe)
{
  if(olde.is_nil()) 
  {
    olde = newe;
  }
  else 
  {
    if(newe.is_nil()) return;
    olde = and_exprt(olde,newe);
  }
}

void summaryt::combine_or(exprt &olde, const exprt &newe)
{
  if(olde.is_nil()) 
  {
    olde = newe;
  }
  else 
  {
    if(newe.is_nil()) return;
    olde = or_exprt(olde,newe);
  }
}

void summaryt::join(const summaryt &new_summary)
{
  assert(params == new_summary.params);
  assert(globals_in == new_summary.globals_in);
  assert(globals_out == new_summary.globals_out);
  combine_or(precondition,new_summary.precondition);
  combine_and(transformer,new_summary.transformer);
  combine_and(invariant,new_summary.invariant);
}
