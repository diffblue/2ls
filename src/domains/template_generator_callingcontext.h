/*******************************************************************\

Module: Template Generator for Calling Contexts

Author: Peter Schrammel

\*******************************************************************/

#ifndef DELTACHECK_TEMPLATE_GENERATOR_CALLINGCONTEXT_H
#define DELTACHECK_TEMPLATE_GENERATOR_CALLINGCONTEXT_H

#include "template_generator_base.h"

class template_generator_callingcontextt : public template_generator_baset
{
public:
  explicit template_generator_callingcontextt(const optionst &_options,
                                    ssa_local_unwindert &_ssa_local_unwinder)
    : template_generator_baset(_options,_ssa_local_unwinder)
  {
  }  

  virtual void operator()(local_SSAt &SSA,
		  local_SSAt::nodest::iterator n_it,
		  local_SSAt::nodet::function_callst::iterator f_it,
                  bool forward=true)
  {
    collect_variables_loop(SSA,forward);
    collect_variables_callingcontext(SSA,n_it,f_it,forward);

    debug() << "Template variables: " << eom;
    domaint::output_var_specs(debug(),var_specs,SSA.ns); debug() << eom;
  }

  virtual domaint::var_sett callingcontext_vars();

protected:
  
  virtual void collect_variables_callingcontext(local_SSAt &SSA,
    local_SSAt::nodest::iterator n_it,
    local_SSAt::nodet::function_callst::iterator f_it,
    bool forward);
};


#endif
