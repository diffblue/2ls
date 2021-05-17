/*******************************************************************\

Module: Template polyhedra domain

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Template polyhedra domain

#ifndef CPROVER_2LS_DOMAINS_TPOLYHEDRA_DOMAIN_H
#define CPROVER_2LS_DOMAINS_TPOLYHEDRA_DOMAIN_H

#include <set>

#include <util/std_expr.h>
#include <util/arith_tools.h>
#include <util/ieee_float.h>
#include <util/options.h>

#include "simple_domain.h"
#include "symbolic_path.h"

class tpolyhedra_domaint:public simple_domaint
{
public:
  /// Template row expression is a simple expression
  struct template_row_exprt:simple_domaint::template_row_exprt, exprt
  {
    explicit template_row_exprt(const exprt &expr) : exprt(expr) {}

    std::vector<exprt> get_row_exprs() override { return {*this}; }
    void output(std::ostream &out, const namespacet &ns) const override;
  };

  /// Row value (parameter) is a constant
  struct row_valuet:constant_exprt
  {
    row_valuet(): constant_exprt(false_exprt()) {}
    explicit row_valuet(const constant_exprt &value) : constant_exprt(value) {}
    using constant_exprt::operator=;

    bool is_inf() const { return get(ID_value)==ID_true; }
    bool is_neg_inf() const { return get(ID_value)==ID_false; }

    exprt get_row_expr(const template_row_exprt &templ_row_expr) const
    {
      if(is_inf())
        return true_exprt();
      if(is_neg_inf())
        return false_exprt();
      // row_expr <= row_value
      return binary_relation_exprt(templ_row_expr, ID_le, *this);
    }
  };

  /// Template value is conjunction of rows
  struct templ_valuet:simple_domaint::valuet, std::vector<row_valuet>
  {
    exprt get_row_expr(rowt row, const template_rowt &templ_row) const override
    {
      auto &templ_row_expr=dynamic_cast<template_row_exprt &>(*templ_row.expr);
      return (*this)[row].get_row_expr(templ_row_expr);
    }

    templ_valuet *clone() override { return new templ_valuet(*this); }
  };

  std::unique_ptr<domaint::valuet> new_value() override
  {
    return std::unique_ptr<domaint::valuet>(new templ_valuet());
  }

  enum strategyt
  {
    ENUMERATION,
    BINSEARCH,
    BINSEARCH2,
    BINSEARCH3
  };
  strategyt strategy;

  tpolyhedra_domaint(
    unsigned _domain_number,
    replace_mapt &_renaming_map,
    const namespacet &_ns,
    const optionst &options):
    simple_domaint(_domain_number, _renaming_map, _ns),
    strategy(options.get_bool_option("enum-solver") ? ENUMERATION : BINSEARCH)
    {}

  // initialize value
  void initialize_value(domaint::valuet &value) override;

  bool edit_row(const rowt &row, valuet &inv, bool improved) override;

  void join(domaint::valuet &value1, const domaint::valuet &value2) override;

  // value -> symbolic bound constraints (for optimization)
  exprt to_symb_pre_constraints(const templ_valuet &value);
  exprt to_symb_pre_constraints(
    const templ_valuet &value,
    const std::set<rowt> &symb_rows);
  exprt to_symb_post_constraints(const std::set<rowt> &symb_rows);
  exprt get_row_symb_value_constraint(
    const rowt &row,
    const row_valuet &row_value,
    bool geq=false);
  exprt get_row_symb_pre_constraint(
    const rowt &row,
    const row_valuet &row_value);
  exprt get_row_symb_post_constraint(const rowt &row);


  // max, min, comparison
  row_valuet get_max_row_value(const rowt &row);
  row_valuet get_min_row_value(const rowt &row);
  row_valuet between(const row_valuet &lower, const row_valuet &upper);
  bool less_than(const row_valuet &v1, const row_valuet &v2);

  // printing
  void output_value(
    std::ostream &out,
    const domaint::valuet &value,
    const namespacet &ns) const override;

  // generating templates
  tpolyhedra_domaint::template_rowt &
  add_template_row(const exprt &expr, const guardst &guards);

  void add_interval_template(
    const var_specst &var_specs,
    const namespacet &ns);
  void add_difference_template(
    const var_specst &var_specs,
    const namespacet &ns);
  void add_sum_template(
    const var_specst &var_specs,
    const namespacet &ns);
  void add_quadratic_template(
    const var_specst &var_specs,
    const namespacet &ns);

  symbol_exprt get_row_symb_value(const rowt &row);

  void rename_for_row(exprt &expr, const rowt &row);

  std::unique_ptr<strategy_solver_baset> new_strategy_solver(
    incremental_solvert &solver,
    const local_SSAt &SSA,
    message_handlert &message_handler) override;

  tpolyhedra_domaint *get_tpolyhedra_domain() override
  {
    return this;
  }

protected:
  friend class strategy_solver_binsearcht;
  friend class strategy_solver_binsearch2t;
  friend class strategy_solver_binsearch3t;
};

#endif
