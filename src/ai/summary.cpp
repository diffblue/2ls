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
  out << "entry vars: ";
  for(summaryt::var_listt::const_iterator it = entry_vars.begin();
      it != entry_vars.end(); it++)
    out << from_expr(ns,"",*it) << " ";
  out << std::endl;
  out << "exit vars: ";
  for(summaryt::var_listt::const_iterator it = exit_vars.begin();
      it != exit_vars.end(); it++)
    out << from_expr(ns,"",*it) << " ";
  out << std::endl;
  out << "precondition: " << from_expr(ns,"",precondition) << std::endl;
  out << "transformer: " << from_expr(ns,"",transformer) << std::endl;
}
