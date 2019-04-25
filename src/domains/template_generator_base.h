/*******************************************************************\

Module: Template Generator Base Class

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Template Generator Base Class

#ifndef CPROVER_2LS_DOMAINS_TEMPLATE_GENERATOR_BASE_H
#define CPROVER_2LS_DOMAINS_TEMPLATE_GENERATOR_BASE_H

#include <util/options.h>
#include <util/replace_expr.h>

#include <ssa/local_ssa.h>
#include <ssa/ssa_unwinder.h>
#include "strategy_solver_base.h"

// #define SHOW_TEMPLATE_VARIABLES
// #define SHOW_TEMPLATE

class template_generator_baset:public messaget
{
public:
  typedef strategy_solver_baset::var_listt var_listt;

  explicit template_generator_baset(
    optionst &_options,
    ssa_dbt &_ssa_db,
    ssa_local_unwindert &_ssa_local_unwinder):
    options(_options), ssa_db(_ssa_db),
    ssa_local_unwinder(_ssa_local_unwinder)
  {
    std_invariants=options.get_bool_option("std-invariants");
  }

  virtual ~template_generator_baset()
  {
    if(domain_ptr!=NULL)
      delete domain_ptr;
  }

  virtual void operator()(
    unsigned _domain_number,
    const local_SSAt &SSA,
    bool forward=true)
  {
    domain_number=_domain_number;
    assert(false);
  }

  virtual domaint::var_sett all_vars();

  inline domaint *domain() { assert(domain_ptr!=NULL); return domain_ptr; }

  domaint::var_specst var_specs;
  replace_mapt post_renaming_map;
  replace_mapt init_renaming_map;
  replace_mapt aux_renaming_map;
  unsigned domain_number; // serves as id for variables names

  optionst options; // copy: we may override options

protected:
  const ssa_dbt &ssa_db;
  const ssa_local_unwindert &ssa_local_unwinder;
  domaint *domain_ptr;
  bool std_invariants; // include value at loop entry

  virtual void collect_variables_loop(
    const local_SSAt &SSA,
    bool forward);

  std::vector<exprt> collect_record_frees(
    const local_SSAt &SSA,
    local_SSAt::nodest::const_iterator loop_begin,
    local_SSAt::nodest::const_iterator loop_end);

  void filter_template_domain();
  void filter_equality_domain();
  void filter_heap_domain();
  void filter_heap_interval_domain();

  void add_var(
    const domaint::vart &var_to_add,
    const domaint::guardt &pre_guard,
    domaint::guardt post_guard,
    const domaint::kindt &kind,
    domaint::var_specst &var_specs);
  void add_vars(
    const var_listt &vars_to_add,
    const domaint::guardt &pre_guard,
    const domaint::guardt &post_guard,
    const domaint::kindt &kind,
    domaint::var_specst &var_specs);
  void add_vars(
    const local_SSAt::var_listt &vars_to_add,
    const domaint::guardt &pre_guard,
    const domaint::guardt &post_guard,
    const domaint::kindt &kind,
    domaint::var_specst &var_specs);
  void add_vars(
    const local_SSAt::var_sett &vars_to_add,
    const domaint::guardt &pre_guard,
    const domaint::guardt &post_guard,
    const domaint::kindt &kind,
    domaint::var_specst &var_specs);

  void get_pre_post_guards(
    const local_SSAt &SSA,
    local_SSAt::nodest::const_iterator n_it,
    exprt &pre_guard,
    exprt &post_guard);
  void get_pre_var(
    const local_SSAt &SSA,
    local_SSAt::objectst::const_iterator o_it,
    local_SSAt::nodest::const_iterator n_it,
    symbol_exprt &pre_var);

  void get_init_expr(
    const local_SSAt &SSA,
    local_SSAt::objectst::const_iterator o_it,
    local_SSAt::nodest::const_iterator n_it,
    exprt &init_expr);

  bool replace_post(replace_mapt replace_map, exprt &expr);
  bool build_custom_expr(
    const local_SSAt &SSA,
    local_SSAt::nodest::const_iterator n_it,
    exprt &expr);

  virtual void handle_special_functions(const local_SSAt &SSA);
  void instantiate_standard_domains(const local_SSAt &SSA);
  bool instantiate_custom_templates(const local_SSAt &SSA);

  void rename_aux_post(symbol_exprt &expr)
  {
    expr.set_identifier(id2string(expr.get_identifier())+"'");
  }
};

#endif // CROVER_2LS_DOMAINS_TEMPLATE_GENERATOR_BASE_H
