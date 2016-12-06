#include "template_generator_acdl.h"
#include <cstdlib>

#define DEBUG

#ifdef DEBUG
#include <iostream>
#endif
#define SHOW_TEMPLATE
#define SHOW_TEMPLATE_VARIABLES

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
  //debug() << "Template variables: " << eom;
  //domaint::output_var_specs(debug(),var_specs,SSA.ns); debug() << eom;
  std::cout << "Template variables: " << std::endl;
  domain_ptr->output_var_specs_info(std::cout, var_specs, SSA.ns) << std::endl;
#endif  
#ifdef SHOW_TEMPLATE
  //debug() << "Template: " << eom;
  //domain_ptr->output_domain(debug(), SSA.ns); debug() << eom;
  std::cout << "Template: " << std::endl;
  domain_ptr->output_domain_info(std::cout, SSA.ns) << std::endl;
#endif
}

/*******************************************************************\

Function: template_generator_acdlt::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void template_generator_acdlt::operator()(const local_SSAt &SSA,
					  const std::set<symbol_exprt> &vars)
{
  clock_t start, finish;
  start = clock();
  for(std::set<symbol_exprt>::const_iterator it = vars.begin();
      it != vars.end(); ++it)
    add_var(*it,true_exprt(),true_exprt(),domaint::OUT,var_specs);
  
  instantiate_standard_domains(SSA);
  finish = clock();
  double time = double(finish - start) / CLOCKS_PER_SEC;
  std::cout << "The total time for template generation is " << time << " s" << std::endl;

#ifdef SHOW_TEMPLATE_VARIABLES
  //debug() << "Template variables: " << eom;
  //domaint::output_var_specs(debug(),var_specs,SSA.ns); debug() << eom;
  std::cout << "Template variables: " << std::endl;
  domain_ptr->output_var_specs_info(std::cout, var_specs, SSA.ns) << std::endl;
#endif  
#ifdef SHOW_TEMPLATE
  //debug() << "Template: " << eom;
  //domain_ptr->output_domain(debug(), SSA.ns); debug() << eom;
  std::cout << "Template: " << std::endl;
  domain_ptr->output_domain_info(std::cout, SSA.ns) << std::endl;
#endif
}


/*******************************************************************\

Function: template_generator_acdlt::positive_template()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void template_generator_acdlt::positive_template(std::vector<exprt> &templates)
{
  domain_ptr->positive_template(templates);
}
