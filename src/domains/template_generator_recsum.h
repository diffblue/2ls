/*******************************************************************\

Module: Template Generator for Recursive Summaries

Author: Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_2LS_TEMPLATE_GENERATOR_RECSUM_H
#define CPROVER_2LS_TEMPLATE_GENERATOR_RECSUM_H

#include "template_generator.h"

class template_generator_recsumt : public template_generatort
{
public:

  explicit template_generator_recsumt(
    optionst &_options,
 		ssa_dbt &_ssa_db,
    ssa_local_unwindert &_ssa_local_unwinder)
    : 
    template_generatort(_options,_ssa_db,_ssa_local_unwinder)
  {
  }  

  virtual void operator()(unsigned _domain_number, 
			  const local_SSAt &SSA, bool forward=true);

  domaint::var_sett inout_vars();

protected:  
  domaint::var_specst var_specs;

  void collect_variables_rec(
    const local_SSAt &SSA);

};


#endif
