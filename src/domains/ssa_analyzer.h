/*******************************************************************\

Module: Data Flow Analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef DELTACHECK_SSA_ANALYZER_H
#define DELTACHECK_SSA_ANALYZER_H

#include <util/replace_expr.h>

#include "../ssa/local_ssa.h"
#include "strategy_solver_base.h"

class ssa_analyzert : public messaget
{
public:
  typedef strategy_solver_baset::constraintst constraintst;
  typedef strategy_solver_baset::var_listt var_listt;
  typedef std::map<local_SSAt::nodet::function_callst::iterator, exprt> calling_contextst;
  typedef std::map<local_SSAt::nodet::function_callst::iterator, domaint::var_sett> 
    calling_context_varst;

  explicit ssa_analyzert(const namespacet &_ns, 
                         const optionst &_options)
    : 
      compute_calling_contexts(false),
      compute_ranking_functions(false),
      ns(_ns),
      options(_options),
      inv_inout(true_exprt()),
      inv_loop(true_exprt()),
      solver_calls(0)
  {
  }  

  void operator()(local_SSAt &SSA, 
                  const exprt &precondition = true_exprt(),
                  bool forward=true);

  void get_postcondition(exprt &result);
  void get_summary(exprt &result);
  void get_loop_invariants(exprt &result);
  void get_calling_contexts(calling_contextst &result);

  bool compute_calling_contexts;
  calling_context_varst calling_context_vars;

  bool compute_ranking_functions;

  unsigned get_number_of_solver_calls() { return solver_calls; }

protected:
  const namespacet &ns;
  const optionst &options;
  exprt inv_out;
  exprt inv_inout;
  exprt inv_loop;
  calling_contextst calling_contexts;
  unsigned iteration_number;
  
  replace_mapt renaming_map;


  // functions for extracting information for template generation

  void collect_variables(local_SSAt &SSA,
			 domaint::var_specst &var_specs,
                         bool forward);
  void generate_template_for_termination(local_SSAt &SSA,
					 linrank_domaint::templatet &templ);

  domaint::var_specst filter_template_domain(const domaint::var_specst& var_specs);
  domaint::var_specst filter_equality_domain(const domaint::var_specst& var_specs);

  void prepare_backward_analysis(local_SSAt &SSA);

  unsigned solver_calls;

private:
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

};


#endif
