/*******************************************************************\

Module: Template Generator Base Class

Author: Peter Schrammel

\*******************************************************************/

#ifndef DELTACHECK_TEMPLATE_GENERATOR_BASE_H
#define DELTACHECK_TEMPLATE_GENERATOR_BASE_H

#include <util/options.h>
#include <util/replace_expr.h>

#include "../ssa/local_ssa.h"
#include "../ssa/ssa_unwinder.h"
#include "strategy_solver_base.h"

class template_generator_baset : public messaget
{
public:
  typedef strategy_solver_baset::var_listt var_listt;

  explicit template_generator_baset(const optionst &_options,
                                    ssa_local_unwindert &_ssa_local_unwinder)
    : 
  options(_options),
  ssa_local_unwinder(_ssa_local_unwinder)
  {
  }  

  virtual void operator()(local_SSAt &SSA, bool forward=true) 
  { 
    assert(false);
  }

  virtual domaint::var_sett all_vars();

  void filter_template_domain();
  void filter_equality_domain();

  domaint::var_specst var_specs;
  replace_mapt renaming_map;

protected:
  const optionst &options;
  const ssa_local_unwindert &ssa_local_unwinder;

  virtual void collect_variables_loop(local_SSAt &SSA,
                         bool forward);

  void add_var(const domaint::vart &var_to_add, 			    
	       const domaint::guardt &pre_guard, 
	       const domaint::guardt &post_guard,
	       const domaint::kindt &kind,
	       domaint::var_specst &var_specs);
  void add_vars(const var_listt &vars_to_add, 			    
		const domaint::guardt &pre_guard, 
		const domaint::guardt &post_guard,
		const domaint::kindt &kind,
		domaint::var_specst &var_specs);
  void add_vars(const local_SSAt::var_listt &vars_to_add,
		const domaint::guardt &pre_guard, 
		const domaint::guardt &post_guard,
		const domaint::kindt &kind,
		domaint::var_specst &var_specs);
  void add_vars(const local_SSAt::var_sett &vars_to_add,
		const domaint::guardt &pre_guard, 
		const domaint::guardt &post_guard,
		const domaint::kindt &kind,
		domaint::var_specst &var_specs);

  void unwinder_rename(symbol_exprt &var,const local_SSAt::nodet &node);

};


#endif
