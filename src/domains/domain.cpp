/*******************************************************************\

Module: Abstract domain base class

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Abstract domain base class

#include "domain.h"
#include "util.h"

/// Abstract value join - not used by most of the domains since the join
/// is typically done between an abstract value and a model of satisfiability
/// in the strategy solver (see method edit_row).
void domaint::join(domaint::valuet &value1, const domaint::valuet &value2)
{
  bool other_bottom=
    value1.basic_value==valuet::OTHER &&
    value2.basic_value==valuet::BOTTOM;
  if(value1.basic_value==value2.basic_value ||
     value1.basic_value==valuet::TOP ||
     other_bottom)
    return;
  value1.basic_value=value2.basic_value;
}

/// Print information about guards to the given output stream.
void guardst::output(std::ostream &out, const namespacet &ns) const
{
  switch(kind)
  {
  case LOOP:
    out << "(LOOP) [ " << from_expr(ns, "", pre_guard) << " | ";
    out << from_expr(ns, "", post_guard) << " | ";
    out << from_expr(ns, "", aux_expr)
        << " ] ===> " << std::endl << "      ";
    break;
  case IN:
    out << "(IN)   ";
    out << from_expr(ns, "", pre_guard) << " ===> "
        << std::endl << "      ";
    break;
  case OUT:
  case OUTL:
    out << "(OUT)  ";
    out << from_expr(ns, "", post_guard) << " ===> "
        << std::endl << "      ";
    break;
  default:
    assert(false);
  }
}

/// Merge two guardst objects into one by conjunction of the guards
guardst guardst::merge_and_guards(
  const guardst &g1,
  const guardst &g2,
  const namespacet &ns)
{
  guardst result;
  // Merge kinds
  const kindt k1=g1.kind;
  const kindt k2=g2.kind;
  result.kind=(k1==OUT || k2==OUT ? (k1==LOOP || k2==LOOP ? OUTL : OUT) :
               (k1==LOOP || k2==LOOP ? LOOP : IN));

  // Merge guards using conjunction
  merge_and(result.pre_guard, g1.pre_guard, g2.pre_guard, ns);
  merge_and(result.post_guard, g1.post_guard, g2.post_guard, ns);
  merge_and(result.aux_expr, g1.aux_expr, g2.aux_expr, ns);

  return result;
}

/// Print information about a variable specification to the given output stream
void var_spect::output(std::ostream &out, const namespacet &ns) const
{
  guards.output(out, ns);
  out << from_expr(ns, "", var) << std::endl;
}

/// Print information about a vector of variable specifications to the given
/// output stream.
void var_specst::output(std::ostream &out, const namespacet &ns) const
{
  for(auto &var_spec : (*this))
    var_spec.output(out, ns);
}
