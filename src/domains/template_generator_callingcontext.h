/*******************************************************************\

Module: Template Generator for Calling Contexts

Author: Peter Schrammel

\*******************************************************************/

#ifndef DELTACHECK_TEMPLATE_GENERATOR_CALLINGCONTEXT_H
#define DELTACHECK_TEMPLATE_GENERATOR_CALLINGCONTEXT_H

#include "template_generator.h"

class template_generator_callingcontextt : public template_generatort
{
public:
  explicit template_generator_callingcontextt(
    optionst &_options,
    ssa_dbt &_ssa_db,
    ssa_local_unwindert &_ssa_local_unwinder)
    : 
    template_generatort(_options,_ssa_db,_ssa_local_unwinder)
  {
  }  

  virtual void operator()(unsigned _domain_number, 
		  const local_SSAt &SSA,
		  local_SSAt::nodest::const_iterator n_it,
		  local_SSAt::nodet::function_callst::const_iterator f_it,
		  bool forward=true);

  domaint::var_sett callingcontext_vars();

protected:
  domaint::var_specst var_specs;
};


#endif
