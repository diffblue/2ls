/*******************************************************************\

Module: Template Generator for Ranking Functions

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef DELTACHECK_TEMPLATE_GENERATOR_RANKING_H
#define DELTACHECK_TEMPLATE_GENERATOR_RANKING_H

#include "template_generator_base.h"

#define LEXICOGRAPHIC

class template_generator_rankingt : public template_generator_baset
{
public:

  explicit template_generator_rankingt(optionst &_options,
                                    ssa_local_unwindert &_ssa_local_unwinder)
    : 
  template_generator_baset(_options,_ssa_local_unwinder)
  {
  }  

  virtual void operator()(const local_SSAt &SSA, bool forward=true);

protected:  

  void collect_variables_ranking(const local_SSAt &SSA,
                         bool forward);

  void filter_ranking_domain(domaint::var_specst &var_specs);

};


#endif
