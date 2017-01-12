/*******************************************************************\

Module: Abstract domain base class

Author: Peter Schrammel

\*******************************************************************/

#include "domain.h"

/*******************************************************************\

Function: domaint::merge_kinds

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

domaint::kindt domaint::merge_kinds(kindt k1, kindt k2)
{
  return
    (k1==OUT || k2==OUT ?  (k1==LOOP || k2==LOOP ?  OUTL : OUT) :
      (k1==LOOP || k2==LOOP ? LOOP :  IN));
}

/*******************************************************************\

Function: domaint::output_var_specs

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::ostream &domaint::output_var_specs(
  std::ostream &out,
  const var_specst &var_specs,
  const namespacet &ns)
{
  for(const auto &v : var_specs)
  {
    switch(v.kind)
    {
    case LOOP:
      out << "(LOOP) [ " << from_expr(ns, "", v.pre_guard) << " | ";
      out << from_expr(ns, "", v.post_guard) << " ]: ";
      break;
    case IN:
      out << "(IN)   ";
      out << from_expr(ns, "", v.pre_guard) << ": ";
      break;
    case OUT: case OUTL:
      out << "(OUT)  ";
      out << from_expr(ns, "", v.post_guard) << ": ";
      break;
    default: assert(false);
    }
    out << from_expr(ns, "", v.var) << std::endl;
  }

  return out;
}
