/*******************************************************************\

Module: Template Generator for ACDL Domain

Author: Peter Schrammel

\*******************************************************************/

#ifndef DELTACHECK_TEMPLATE_GENERATOR_ACDL_H
#define DELTACHECK_TEMPLATE_GENERATOR_ACDL_H

#include "../domains/template_generator_base.h"

class template_generator_acdlt : public template_generator_baset
{
public:

  explicit template_generator_acdlt(optionst &_options,
 				   ssa_dbt &_ssa_db,
                                   ssa_local_unwindert &_ssa_local_unwinder)
    : 
  template_generator_baset(_options,_ssa_db,_ssa_local_unwinder)
  {
  }  


  void operator()(const local_SSAt &SSA, const symbol_exprt& var);
  void operator()(const local_SSAt &SSA, const std::set<symbol_exprt> &vars);

  void positive_template(std::vector<exprt> &templates);
  
  domaint::var_sett out_vars();

};


#endif
