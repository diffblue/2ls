#include "template_generator_acdl.h"

#define SHOW_TEMPLATE

/*******************************************************************\

Function: template_generator_acdlt::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void template_generator_acdlt::operator()(const local_SSAt &SSA, const symbol_exprt &var)
{
  add_var(var,true_exprt(),true_exprt(),domaint::OUT,var_specs);
  
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
