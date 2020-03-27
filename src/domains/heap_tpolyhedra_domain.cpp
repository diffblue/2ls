/*******************************************************************\

Module: Combination of heap and template polyhedra abstract domains

Author: Viktor Malik

\*******************************************************************/

/// \file
/// Combination of heap and template polyhedra abstract domains

#include "heap_tpolyhedra_domain.h"

/// Initialize abstract value.
void heap_tpolyhedra_domaint::initialize_value(domaint::valuet &value)
{
  heap_tpolyhedra_valuet &v=static_cast<heap_tpolyhedra_valuet &>(value);

  heap_domain.initialize_value(v.heap_value);
  polyhedra_domain.initialize_value(v.tpolyhedra_value);
}

void heap_tpolyhedra_domaint::output_value(
  std::ostream &out,
  const domaint::valuet &value,
  const namespacet &ns) const
{
  const heap_tpolyhedra_valuet &v=
    static_cast<const heap_tpolyhedra_valuet &>(value);

  heap_domain.output_value(out, v.heap_value, ns);
  polyhedra_domain.output_value(out, v.tpolyhedra_value, ns);
}

void heap_tpolyhedra_domaint::output_domain(
  std::ostream &out,
  const namespacet &ns) const
{
  heap_domain.output_domain(out, ns);
  polyhedra_domain.output_domain(out, ns);
}

void heap_tpolyhedra_domaint::project_on_vars(
  domaint::valuet &value,
  const var_sett &vars,
  exprt &result)
{
  heap_tpolyhedra_valuet &v=static_cast<heap_tpolyhedra_valuet &>(value);

  exprt heap_result;
  heap_domain.project_on_vars(v.heap_value, vars, heap_result);
  exprt tpolyhedra_result;
  polyhedra_domain.project_on_vars(v.tpolyhedra_value, vars, tpolyhedra_result);

  result=heap_result;
  if(tpolyhedra_result!=true_exprt())
    result=and_exprt(result, tpolyhedra_result);
}

/// Restrict template to a given symbolic path.
/// \param sympath: Symbolic path
void heap_tpolyhedra_domaint::restrict_to_sympath(
  const symbolic_patht &sympath)
{
  heap_domain.restrict_to_sympath(sympath);
  polyhedra_domain.restrict_to_sympath(sympath);
}

/// Reset aux symbols to true (remove all restricitions).
void heap_tpolyhedra_domaint::remove_all_sympath_restrictions()
{
  heap_domain.remove_all_sympath_restrictions();
  polyhedra_domain.remove_all_sympath_restrictions();
}

/// Restrict template to other paths than those specified.
/// \param sympaths: Vector of symbolic paths
void heap_tpolyhedra_domaint::eliminate_sympaths(
  const std::vector<symbolic_patht> &sympaths)
{
  heap_domain.eliminate_sympaths(sympaths);
  polyhedra_domain.eliminate_sympaths(sympaths);
}

/// Undo last restriction.
void heap_tpolyhedra_domaint::undo_sympath_restriction()
{
  heap_domain.undo_sympath_restriction();
  polyhedra_domain.undo_sympath_restriction();
}
