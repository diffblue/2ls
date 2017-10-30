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
  interval_domain.initialize(v.interval_value);
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
  interval_domain.output_value(out, v.interval_value, ns);
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
  interval_domain.output_domain(out, ns);
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
  interval_domain.project_on_vars(v.interval_value, vars, interval_result);

  result=heap_result;
  if(interval_result!=true_exprt())
    result=and_exprt(result, interval_result);
}
