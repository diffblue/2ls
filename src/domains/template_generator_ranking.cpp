/*******************************************************************\

Module: Template Generator for Ranking Functions

Author: Peter Schrammel

\*******************************************************************/

#include "template_generator_ranking.h"

#include <util/find_symbols.h>
#include <util/arith_tools.h>
#include <util/simplify_expr.h>
#include <util/mp_arith.h>

#ifdef DEBUG
#include <iostream>
#endif

/*******************************************************************\

Function: template_generator_rankingt::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void template_generator_rankingt::operator()(const local_SSAt &SSA,  bool forward)
{
  handle_special_functions(SSA); // we have to call that to prevent trouble!

  collect_variables_ranking(SSA,forward);

  instantiate_standard_domains(SSA);

#if 1
  debug() << "Template variables: " << eom;
  domaint::output_var_specs(debug(),var_specs,SSA.ns); debug() << eom;
  debug() << "Template: " << eom;
  domain_ptr->output_domain(debug(), SSA.ns); debug() << eom;
#endif  
}

/*******************************************************************\

Function: template_generator_rankingt::collect_variables_ranking

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void template_generator_rankingt::collect_variables_ranking(const local_SSAt &SSA,bool forward)
{
  collect_variables_loop(SSA,forward);
}

