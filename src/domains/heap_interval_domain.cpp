/*******************************************************************\

Module: Combination of heap and interval abstract domains

Author: Viktor Malik

\*******************************************************************/

#include "heap_interval_domain.h"

/*******************************************************************\

Function: heap_interval_domaint::initialize

  Inputs:

 Outputs:

 Purpose: Initialize abstract value.

\*******************************************************************/

void heap_interval_domaint::initialize(domaint::valuet &value)
{
  heap_interval_valuet &v=static_cast<heap_interval_valuet &>(value);

  heap_domain.initialize(v.heap_value);
  polyhedra_domain.initialize(v.interval_value);
}

/*******************************************************************\

Function: heap_interval_domaint::output_value

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void heap_interval_domaint::output_value(
  std::ostream &out,
  const domaint::valuet &value,
  const namespacet &ns) const
{
  const heap_interval_valuet &v=
    static_cast<const heap_interval_valuet &>(value);

  heap_domain.output_value(out, v.heap_value, ns);
  polyhedra_domain.output_value(out, v.interval_value, ns);
}

/*******************************************************************\

Function: heap_interval_domaint::output_domain

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void heap_interval_domaint::output_domain(
  std::ostream &out,
  const namespacet &ns) const
{
  heap_domain.output_domain(out, ns);
  polyhedra_domain.output_domain(out, ns);
}

/*******************************************************************\

Function: heap_interval_domaint::project_on_vars

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void heap_interval_domaint::project_on_vars(
  domaint::valuet &value,
  const domaint::var_sett &vars,
  exprt &result)
{
  heap_interval_valuet &v=static_cast<heap_interval_valuet &>(value);

  exprt heap_result;
  heap_domain.project_on_vars(v.heap_value, vars, heap_result);
  exprt interval_result;
  polyhedra_domain.project_on_vars(v.interval_value, vars, interval_result);

  result=heap_result;
  if(interval_result!=true_exprt())
    result=and_exprt(result, interval_result);
}

/*******************************************************************\

Function: heap_interval_domaint::restrict_to_sympath

  Inputs: Symbolic path

 Outputs:

 Purpose: Restrict template to a given symbolic path.

\*******************************************************************/
void heap_interval_domaint::restrict_to_sympath(
  const symbolic_patht &sympath)
{
  heap_domain.restrict_to_sympath(sympath);
  polyhedra_domain.restrict_to_sympath(sympath);
}

/*******************************************************************\

Function: heap_interval_domaint::clear_aux_symbols

  Inputs:

 Outputs:

 Purpose: Reset aux symbols to true (remove all restricitions).

\*******************************************************************/
void heap_interval_domaint::clear_aux_symbols()
{
  heap_domain.clear_aux_symbols();
  polyhedra_domain.clear_aux_symbols();
}

/*******************************************************************\

Function: heap_interval_domaint::eliminate_sympaths

  Inputs: Vector of symbolic paths

 Outputs:

 Purpose: Restrict template to other paths than those specified.

\*******************************************************************/
void heap_interval_domaint::eliminate_sympaths(
  const std::vector<symbolic_patht> &sympaths)
{
  heap_domain.eliminate_sympaths(sympaths);
  polyhedra_domain.eliminate_sympaths(sympaths);
}

/*******************************************************************\

Function: heap_interval_domaint::undo_restriction

  Inputs:

 Outputs:

 Purpose: Undo last restriction.

\*******************************************************************/
void heap_interval_domaint::undo_restriction()
{
  heap_domain.undo_restriction();
  polyhedra_domain.undo_restriction();
}
