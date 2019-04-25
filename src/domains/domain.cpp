/*******************************************************************\

Module: Abstract domain base class

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Abstract domain base class

#include "domain.h"

domaint::kindt domaint::merge_kinds(kindt k1, kindt k2)
{
  return
    (k1==OUT || k2==OUT ?  (k1==LOOP || k2==LOOP ?  OUTL : OUT) :
      (k1==LOOP || k2==LOOP ? LOOP :  IN));
}

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

exprt domaint::get_current_loop_guard(size_t row)
{
  return true_exprt();
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
