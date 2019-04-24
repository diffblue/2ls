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

#include "domain.h"
#include "symbolic_path.h"

class tpolyhedra_domaint:public domaint
{
public:
  typedef exprt row_exprt;
  typedef constant_exprt row_valuet; // "bound"

  class templ_valuet:public domaint::valuet, public std::vector<row_valuet>
  {
  };

  typedef struct
  {
    guardt pre_guard;
    guardt post_guard;
    row_exprt expr;
    exprt aux_expr;
    kindt kind;
  } template_rowt;

  typedef std::vector<template_rowt> templatet;

  tpolyhedra_domaint(
    unsigned _domain_number,
    replace_mapt &_renaming_map,
    const namespacet &_ns):
    domaint(_domain_number, _renaming_map, _ns)
  {
  }

  // initialize value
  virtual void initialize(valuet &value);

  std::vector<exprt> get_required_smt_values(size_t row);
  void set_smt_values(std::vector<exprt> got_values, size_t row);

  bool edit_row(const rowt &row, valuet &inv, bool improved);

  exprt to_pre_constraints(valuet &_value);

  void make_not_post_constraints(
    valuet &_value,
    exprt::operandst &cond_exprs);

  virtual void join(valuet &value1, const valuet &value2);

  // value -> constraints
  exprt get_row_constraint(const rowt &row, const row_valuet &row_value);
  exprt get_row_pre_constraint(const rowt &row, const row_valuet &row_value);
  exprt get_row_post_constraint(const rowt &row, const row_valuet &row_value);
  exprt get_row_pre_constraint(const rowt &row, const templ_valuet &value);
  exprt get_row_post_constraint(const rowt &row, const templ_valuet &value);

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


  // set, get value
  row_valuet get_row_value(const rowt &row, const templ_valuet &value);
  void set_row_value(
    const rowt &row,
    const row_valuet &row_value,
    templ_valuet &value);

  // max, min, comparison
  row_valuet get_max_row_value(const rowt &row);
  row_valuet get_min_row_value(const rowt &row);
  row_valuet between(const row_valuet &lower, const row_valuet &upper);
  bool less_than(const row_valuet &v1, const row_valuet &v2);
  bool is_row_value_inf(const row_valuet & row_value) const;
  bool is_row_value_neginf(const row_valuet & row_value) const;

  // printing
  virtual void output_value(
    std::ostream &out,
    const valuet &value,
    const namespacet &ns) const;
  virtual void output_domain(
    std::ostream &out,
    const namespacet &ns) const;

  // projection
  virtual void project_on_vars(
    valuet &value,
    const var_sett &vars,
    exprt &result);

  unsigned template_size();

  // generating templates
  template_rowt &add_template_row(
    const exprt& expr,
    const exprt& pre_guard,
    const exprt& post_guard,
    const exprt& aux_expr,
    kindt kind);

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

  void restrict_to_sympath(const symbolic_patht &sympath);
  void undo_restriction();
  void eliminate_sympaths(const std::vector<symbolic_patht> &sympaths);
  void clear_aux_symbols();

  symbol_exprt get_row_symb_value(const rowt &row);

  void rename_for_row(exprt &expr, const rowt &row);

protected:
  friend class strategy_solver_binsearcht;
  friend class strategy_solvert;

  templatet templ;
  exprt value;
};

#endif
