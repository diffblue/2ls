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
#include <ssa/ssa_db.h>
#include <ssa/unwinder.h>
#include "strategy_solver_base.h"

// #define SHOW_TEMPLATE_VARIABLES
// #define SHOW_TEMPLATE

class template_generator_baset:public messaget
{
public:
  explicit template_generator_baset(optionst &_options,
                                    const ssa_dbt &_ssa_db,
                                    const local_unwindert &_ssa_local_unwinder,
                                    incremental_solvert *solver = nullptr)
    : options(_options),
      ssa_db(_ssa_db),
      ssa_local_unwinder(_ssa_local_unwinder),
      solver(solver)
  {
    std_invariants=options.get_bool_option("std-invariants");
  }

  template_generator_baset(template_generator_baset &other)
    : template_generator_baset(other.options,
                               other.ssa_db,
                               other.ssa_local_unwinder,
                               other.solver)
  {
  }

  virtual void operator()(
    unsigned _domain_number,
    const local_SSAt &SSA,
    bool forward=true)
  {
    domain_number=_domain_number;
    assert(false);
  }

  virtual var_sett all_vars();

  inline domaint *domain()
  {
    assert(domain_ptr);
    return domain_ptr.get();
  }

  std::unique_ptr<domaint> get_domain()
  {
    return std::move(domain_ptr);
  };

  var_specst all_var_specs;
  replace_mapt post_renaming_map;
  replace_mapt init_renaming_map;
  replace_mapt aux_renaming_map;
  unsigned domain_number; // serves as id for variables names

  optionst options; // copy: we may override options

protected:
  const ssa_dbt &ssa_db;
  const local_unwindert &ssa_local_unwinder;
  incremental_solvert *solver = nullptr;
  std::unique_ptr<domaint> domain_ptr;
  bool std_invariants; // include value at loop entry

  virtual void collect_variables_loop(
    const local_SSAt &SSA,
    bool forward);

  std::vector<exprt> collect_record_frees(
    const local_SSAt &SSA,
    local_SSAt::nodest::const_iterator loop_begin,
    local_SSAt::nodest::const_iterator loop_end);

  static var_specst filter_template_domain(const var_specst &var_specs);
  static var_specst filter_equality_domain(const var_specst &var_specs);
  static var_specst filter_heap_domain(const var_specst &var_specs);
  static var_specst filter_array_domain(const var_specst &var_specs);

  void add_var(const vart &var,
               const guardst::guardt &pre_guard,
               guardst::guardt post_guard,
               const guardst::kindt &kind,
               const var_listt &related_vars,
               locationt loc,
               var_specst &var_specs);
  void add_vars(const var_listt &vars_to_add,
                const guardst::guardt &pre_guard,
                const guardst::guardt &post_guard,
                const guardst::kindt &kind,
                locationt loc,
                var_specst &var_specs);
  void add_vars(const local_SSAt::var_listt &vars_to_add,
                const guardst::guardt &pre_guard,
                const guardst::guardt &post_guard,
                const guardst::kindt &kind,
                locationt loc,
                var_specst &var_specs);
  void add_vars(const local_SSAt::var_sett &vars_to_add,
                const guardst::guardt &pre_guard,
                const guardst::guardt &post_guard,
                const guardst::kindt &kind,
                locationt loc,
                var_specst &var_specs);

  void get_pre_post_guards(
    const local_SSAt &SSA,
    local_SSAt::nodest::const_iterator n_it,
    exprt &pre_guard,
    exprt &post_guard);
  symbol_exprt get_pre_var(
    const local_SSAt &SSA,
    local_SSAt::objectst::const_iterator o_it,
    local_SSAt::nodest::const_iterator n_it);

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

  void replace_array_index_loop(exprt &index,
                                local_SSAt::nodest::const_iterator n_it,
                                const local_SSAt &SSA,
                                const ssa_domaint::phi_nodest &phi_nodes);

  virtual void handle_special_functions(const local_SSAt &SSA);
  std::unique_ptr<domaint>
  instantiate_standard_domains(const var_specst &var_specs_,
                               const local_SSAt &SSA,
                               replace_mapt *renaming_map_ = nullptr);
  bool instantiate_custom_templates(const local_SSAt &SSA);

  void rename_aux_post(symbol_exprt &expr)
  {
    expr.set_identifier(id2string(expr.get_identifier())+"'");
  }

  friend class array_domaint;
};

#endif // CROVER_2LS_DOMAINS_TEMPLATE_GENERATOR_BASE_H
