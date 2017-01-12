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
  add_var(var, true_exprt(), true_exprt(), domaint::OUT, var_specs);

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

/*******************************************************************\

Function: template_generator_acdlt::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void template_generator_acdlt::operator()(const local_SSAt &SSA,
                                          const std::set<symbol_exprt> &vars)
{
#ifdef SHOW_TEMPLATE_VARIABLES
  clock_t start, finish;
  start=clock();
#endif
  // Avoid template generation on return_values
  /*for(std::set<symbol_exprt>::const_iterator it=vars.begin();
    it!=vars.end(); ++it)
    {
    const irep_idt &name=it->get(ID_identifier);
    std::string s=id2string(name);
    size_t found;
    if ((found=name.find("return_value"))!=std::string::npos)
    tmp_var.insert(*it);
    }*/
  for(std::set<symbol_exprt>::const_iterator it=vars.begin();
      it!=vars.end(); ++it) {
    /*const irep_idt &name=it->get(ID_identifier);
      std::string s=id2string(name);
      size_t found;
      if ((found=s.find("return_value"))!=std::string::npos)
      continue; */
    add_var(*it, true_exprt(), true_exprt(), domaint::OUT, var_specs);
  }

  instantiate_standard_domains(SSA);
#ifdef SHOW_TEMPLATE_VARIABLES
  finish=clock();
  double time=double(finish-start) / CLOCKS_PER_SEC;
  std::cout << "The total time for template generation is " << time << " s" << std::endl;
#endif

#ifdef SHOW_TEMPLATE_VARIABLES
  std::cout << "Template variables: " << std::endl;
  domaint::output_var_specs(std::cout, var_specs, SSA.ns) << std::endl;
#endif
#ifdef SHOW_TEMPLATE
  std::cout << "Template: " << std::endl;
  domain_ptr->output_domain(std::cout, SSA.ns);
  std::cout << std::endl;
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
