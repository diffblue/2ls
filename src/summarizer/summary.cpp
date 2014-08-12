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
}
