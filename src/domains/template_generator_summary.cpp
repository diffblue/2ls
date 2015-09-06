/*******************************************************************\

Module: Template Generator for Summaries, Invariants and Preconditions

Author: Peter Schrammel

\*******************************************************************/

#include "template_generator_summary.h"
#include "equality_domain.h"
#include "tpolyhedra_domain.h"

#include <util/find_symbols.h>
#include <util/arith_tools.h>
#include <util/simplify_expr.h>
#include <util/mp_arith.h>

#ifdef DEBUG
#include <iostream>
#endif

/*******************************************************************\

Function: template_generator_summaryt::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void template_generator_summaryt::operator()(unsigned _domain_number, 
			  const local_SSAt &SSA,  bool forward)
{
  domain_number = _domain_number;
  handle_special_functions(SSA); // we have to call that to prevent trouble!

  collect_variables_loop(SSA,forward);

  // do not compute summary for entry-point
  if(SSA.goto_function.body.instructions.front().function != ID__start ||
     options.get_bool_option("preconditions"))
    collect_variables_inout(SSA,forward);

  // either use standard templates or user-supplied ones
  if(!instantiate_custom_templates(SSA))
    instantiate_standard_domains(SSA);

#ifdef SHOW_TEMPLATE_VARIABLES
  debug() << "Template variables: " << eom;
  domaint::output_var_specs(debug(),var_specs,SSA.ns); debug() << eom;
#endif  
#ifdef SHOW_TEMPLATE
  debug() << "Template: " << eom;
  domain_ptr->output_domain(debug(), SSA.ns); debug() << eom;
#endif  
}

/*******************************************************************\

Function: template_generator_summaryt::collect_variables_inout

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void template_generator_summaryt::collect_variables_inout(const local_SSAt &SSA,bool forward)
{
  // add params and globals_in
  exprt first_guard = SSA.guard_symbol(SSA.goto_function.body.instructions.begin());
  add_vars(SSA.params,first_guard,first_guard,
           forward ? domaint::IN : domaint::OUT,
           var_specs);
  add_vars(SSA.globals_in,first_guard,first_guard,
           forward ? domaint::IN : domaint::OUT,
           var_specs);

  // add globals_out (includes return values)
  exprt last_guard = 
    SSA.guard_symbol(--SSA.goto_function.body.instructions.end());
  add_vars(SSA.globals_out,last_guard,last_guard,
	   forward ? domaint::OUT : domaint::IN,
	   var_specs);
}

/*******************************************************************\

Function: template_generator_summaryt::inout_vars

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

domaint::var_sett template_generator_summaryt::inout_vars()
{
  domaint::var_sett vars;
  for(domaint::var_specst::const_iterator v = var_specs.begin(); 
      v!=var_specs.end(); v++)
  {
    if(v->kind==domaint::IN || v->kind==domaint::OUT) vars.insert(v->var);
  }
  return vars;
}

/*******************************************************************\

Function: template_generator_summaryt::out_vars

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

domaint::var_sett template_generator_summaryt::out_vars()
{
  domaint::var_sett vars;
  for(domaint::var_specst::const_iterator v = var_specs.begin(); 
      v!=var_specs.end(); v++)
  {
    if(v->kind==domaint::OUT) vars.insert(v->var);
  }
  return vars;
}

/*******************************************************************\

Function: template_generator_summaryt::loop_vars

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

domaint::var_sett template_generator_summaryt::loop_vars()
{
  domaint::var_sett vars;
  for(domaint::var_specst::const_iterator v = var_specs.begin(); 
      v!=var_specs.end(); v++)
  {
    if(v->kind==domaint::LOOP || v->kind==domaint::IN) 
      vars.insert(v->var);
  }
  return vars;
}
