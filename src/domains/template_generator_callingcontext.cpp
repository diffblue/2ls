/*******************************************************************\

Module: Template Generator for Calling Contexts

Author: Peter Schrammel

\*******************************************************************/

#include "template_generator_callingcontext.h"
#include "equality_domain.h"
#include "tpolyhedra_domain.h"

#include <util/find_symbols.h>

/*******************************************************************\

Function: template_generator_callingcontextt::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void template_generator_callingcontextt::operator()(
  unsigned _domain_number, 
  const local_SSAt &SSA,
  local_SSAt::nodest::const_iterator n_it,
  local_SSAt::nodet::function_callst::const_iterator f_it,
  bool forward)
{
  domain_number = _domain_number;
  handle_special_functions(SSA); // we have to call that to prevent trouble!

  collect_variables_loop(var_specs, SSA,forward);
  if(forward)
    collect_input_variables_callingcontext(var_specs, SSA,n_it,f_it);
  else
    collect_output_variables_callingcontext(var_specs, SSA,n_it,f_it);

  //get domain from command line options
  instantiate_standard_domains(var_specs, SSA);  

#if 1
  debug() << "Template variables: " << eom;
  domaint::output_var_specs(debug(),var_specs,SSA.ns); debug() << eom;
  debug() << "Template: " << eom;
  domain_ptr->output_domain(debug(), SSA.ns); debug() << eom;
#endif  
}

/*******************************************************************\

Function: template_generator_callingcontextt::callingcontext_vars

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

domaint::var_sett template_generator_callingcontextt::callingcontext_vars()
{
  domaint::var_sett vars;
  for(domaint::var_specst::const_iterator v = var_specs.begin(); 
      v!=var_specs.end(); v++)
  {
    if(v->kind==domaint::OUT) vars.insert(v->var);
  }
  return vars;
}
