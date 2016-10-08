/*******************************************************************\

Module: Template Generator for Ranking Functions

Author: Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_2LS_TEMPLATE_GENERATOR_RANKING_H
#define CPROVER_2LS_TEMPLATE_GENERATOR_RANKING_H

#include "template_generator.h"

class template_generator_rankingt : public template_generatort
{
public:

  explicit template_generator_rankingt(
    optionst &_options,
    ssa_dbt &_ssa_db,
    ssa_local_unwindert &_ssa_local_unwinder)
    : 
    template_generatort(_options,_ssa_db,_ssa_local_unwinder)
  {
  }  

  virtual void operator()(unsigned _domain_number,
			  const local_SSAt &SSA, bool forward=true);

  virtual domaint::var_sett all_vars();

protected:  
  domaint::var_specst var_specs;

  void collect_variables_ranking(
    domaint::var_specst &var_specs,
    const local_SSAt &SSA,
    bool forward);

  void filter_ranking_domain(domaint::var_specst &var_specs);

};


#endif
