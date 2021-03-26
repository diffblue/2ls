/*******************************************************************\

Module: Template Generator for Summaries, Invariants and Preconditions

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Template Generator for Summaries, Invariants and Preconditions

#define SHOW_TEMPLATE

#include "template_generator_summary.h"
#include "equality_domain.h"
#include "tpolyhedra_domain.h"
#include "domain.h"

#include <util/find_symbols.h>
#include <util/arith_tools.h>
#include <util/simplify_expr.h>
#include <util/mp_arith.h>

#ifdef DEBUG
#include <iostream>
#endif

void template_generator_summaryt::operator()(
  unsigned _domain_number,
  const local_SSAt &SSA,
  bool forward)
{
  domain_number=_domain_number;
  handle_special_functions(SSA); // we have to call that to prevent trouble!

  collect_variables_loop(SSA, forward);

  // do not compute summary for entry-point
  if(SSA.goto_function.body.instructions.front().function!=
     goto_functionst::entry_point() ||
     options.get_bool_option("preconditions"))
    collect_variables_inout(SSA, forward);

  // either use standard templates or user-supplied ones
  if(!instantiate_custom_templates(SSA))
    instantiate_standard_domains(SSA);

#ifdef SHOW_TEMPLATE_VARIABLES
  debug() << "Template variables: " << eom;
  domaint::output_var_specs(debug(), var_specs, SSA.ns); debug() << eom;
#endif
#ifdef SHOW_TEMPLATE
  debug() << "Template: " << eom;
  domain_ptr->output_domain(debug(), SSA.ns); debug() << eom;
#endif
}

void template_generator_summaryt::collect_variables_inout(
  const local_SSAt &SSA,
  bool forward)
{
  // add params and globals_in
  exprt first_guard=
    SSA.guard_symbol(SSA.goto_function.body.instructions.begin());
  add_vars(
    SSA.params,
    first_guard,
    first_guard,
    forward ? guardst::IN : guardst::OUT,
    var_specs);
  add_vars(
    SSA.globals_in,
    first_guard,
    first_guard,
    forward ? guardst::IN : guardst::OUT,
    var_specs);

  // add globals_out (includes return values)
  exprt last_guard=
    SSA.guard_symbol(--SSA.goto_function.body.instructions.end());
  add_vars(
    SSA.globals_out,
    last_guard,
    last_guard,
    forward ? guardst::OUT : guardst::IN,
    var_specs);
}

var_sett template_generator_summaryt::inout_vars()
{
  var_sett vars;
  for(var_specst::const_iterator v=var_specs.begin();
      v!=var_specs.end(); v++)
  {
    if(v->guards.kind==guardst::IN ||
       v->guards.kind==guardst::OUT)
      vars.insert(v->var);
  }
  return vars;
}

var_sett template_generator_summaryt::out_vars()
{
  var_sett vars;
  for(var_specst::const_iterator v=var_specs.begin();
      v!=var_specs.end(); v++)
  {
    if(v->guards.kind==guardst::OUT)
      vars.insert(v->var);
  }
  return vars;
}

var_sett template_generator_summaryt::loop_vars()
{
  var_sett vars;
  for(var_specst::const_iterator v=var_specs.begin();
      v!=var_specs.end(); v++)
  {
    if(v->guards.kind==guardst::LOOP || v->guards.kind==guardst::IN)
      vars.insert(v->var);
  }
  return vars;
}
