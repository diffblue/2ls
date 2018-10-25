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

void domaint::output_var_specs(
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
}

const exprt domaint::initialize_solver(
  const local_SSAt &SSA,
  const exprt &precondition,
  template_generator_baset &template_generator)
{
  return true_exprt();
}

void domaint::solver_iter_init(valuet &value)
{
}

bool domaint::has_something_to_solve()
{
  return true;
}

bool domaint::handle_unsat(valuet &value, bool improved)
{
  return improved;
}

void domaint::post_edit()
{
}

exprt domaint::make_permanent(valuet &value)
{
  return true_exprt();
}
