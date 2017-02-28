/*******************************************************************\

Module: SSA var collector class

Author: Peter Schrammel, Stefan Marticek

\*******************************************************************/

#ifndef CPROVER_SSA_VAR_COLLECTOR_H
#define CPROVER_SSA_VAR_COLLECTOR_H

#include <util/options.h>

#include "local_ssa.h"
#include "ssa_unwinder.h"

#include "../domains/strategy_solver_base.h"

class ssa_var_collectort
{
public:

  typedef goto_programt::const_targett locationt;

  typedef struct loop_vart
  {
    loop_vart(exprt _init_expr, exprt _phi_expr, locationt _location)
      : init_expr(_init_expr), phi_expr(_phi_expr), location(_location)
    {
    }
    exprt init_expr;
    exprt phi_expr;
    locationt location;
  } loop_vart;

  typedef std::vector<loop_vart> loop_varst;
  typedef std::vector<loop_varst> func_loop_varst;
    
  virtual func_loop_varst collect_variables_loop(const local_SSAt &SSA,
                       bool forward, const namespacet &ns);

  typedef strategy_solver_baset::var_listt var_listt;

  explicit ssa_var_collectort(optionst &_options,
                                  ssa_local_unwindert &_ssa_local_unwinder)
  :
  options(_options),
  ssa_local_unwinder(_ssa_local_unwinder)
  {
    std_invariants = options.get_bool_option("std-invariants");
  }
    
protected:

  domaint::var_specst var_specs;
  replace_mapt post_renaming_map;
  replace_mapt init_renaming_map;
  replace_mapt aux_renaming_map;

  optionst options; // copy: we may override options

  void add_var(const domaint::vart &var_to_add,
       const domaint::guardt &pre_guard,
       domaint::guardt post_guard,
       const domaint::kindt &kind,
       domaint::var_specst &var_specs);

  void get_pre_post_guards(const local_SSAt &SSA,
       local_SSAt::nodest::const_iterator n_it,
       exprt &pre_guard, exprt &post_guard);

  void get_pre_var(const local_SSAt &SSA,
                   local_SSAt::objectst::const_iterator o_it,
                   local_SSAt::nodest::const_iterator n_it,
                   symbol_exprt &pre_var);

  void get_init_expr(const local_SSAt &SSA,
                   local_SSAt::objectst::const_iterator o_it,
                   local_SSAt::nodest::const_iterator n_it,
                   exprt &init_expr);

  void rename_aux_post(symbol_exprt &expr)
  {
    expr.set_identifier(id2string(expr.get_identifier())+"'");
  }

  bool std_invariants; //include value at loop entry
  const ssa_local_unwindert &ssa_local_unwinder;
};

#endif /* CPROVER_SSA_VAR_COLLECTOR_H */

