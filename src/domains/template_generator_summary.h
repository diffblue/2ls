/*******************************************************************\

Module: Template Generator for Summaries

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef DELTACHECK_TEMPLATE_GENERATOR_SUMMARY_H
#define DELTACHECK_TEMPLATE_GENERATOR_SUMMARY_H

#include "template_generator_base.h"

class template_generator_summaryt : public template_generator_baset
{
public:

  explicit template_generator_summaryt(const optionst &_options,
                                    ssa_local_unwindert &_ssa_local_unwinder)
    : 
  template_generator_baset(_options,_ssa_local_unwinder)
  {
  }  

  virtual void operator()(local_SSAt &SSA, 
                  bool forward=true)
  {
    collect_variables_loop(SSA,forward);
    collect_variables_inout(SSA,forward);

    debug() << "Template variables: " << eom;
    domaint::output_var_specs(debug(),var_specs,SSA.ns); debug() << eom;
  }

  virtual domaint::var_sett inout_vars();
  virtual domaint::var_sett loop_vars();
  virtual domaint::var_sett out_vars();

protected:  

  virtual void collect_variables_inout(local_SSAt &SSA,
                         bool forward);

};


#endif
