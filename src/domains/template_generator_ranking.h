/*******************************************************************\

Module: Template Generator for Ranking Functions

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef DELTACHECK_TEMPLATE_GENERATOR_RANKING_H
#define DELTACHECK_TEMPLATE_GENERATOR_RANKING_H

#include "template_generator_base.h"

class template_generator_rankingt : public template_generator_baset
{
public:

  explicit template_generator_rankingt(const optionst &_options,
                                    ssa_local_unwindert &_ssa_local_unwinder)
    : 
  template_generator_baset(_options,_ssa_local_unwinder)
  {
  }  

  virtual void operator()(local_SSAt &SSA, 
                  bool forward=true)
  {
    collect_variables_ranking(SSA,forward);

    debug() << "Template variables: " << eom;
    domaint::output_var_specs(debug(),var_specs,SSA.ns); debug() << eom;
  }

protected:  

  virtual void collect_variables_ranking(local_SSAt &SSA,
                         bool forward);

};


#endif
