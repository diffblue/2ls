/*******************************************************************\

Module: Abstract domain for representing heap

Author: Viktor Malik

\*******************************************************************/
/// \file
/// Abstract domain for representing heap

#ifndef CPROVER_2LS_DOMAINS_HEAP_DOMAIN_H
#define CPROVER_2LS_DOMAINS_HEAP_DOMAIN_H

#include <memory>

#include <util/namespace.h>
#include <util/message.h>

#include <ssa/local_ssa.h>

#include "domain.h"
#include "template_generator_base.h"
#include <ssa/ssa_inliner.h>

class heap_domaint:public domaint
{
public:
  typedef unsigned rowt;

  heap_domaint(
    unsigned int _domain_number,
    replace_mapt &_renaming_map,
    const var_specst &var_specs,
    const local_SSAt &SSA):
    domaint(_domain_number, _renaming_map, SSA.ns)
  {
    make_template(var_specs, ns);
  }

  struct template_rowt
  {
    vart expr;
    guardt pre_guard;
    guardt post_guard;
    exprt aux_expr;
    kindt kind;
  };
  typedef std::vector<template_rowt> templatet;

  /*******************************************************************\
  Value of a template row
  \*******************************************************************/
  struct row_valuet
  {
    // Set of objects (or NULL) the row variable can point to
    std::set<exprt> points_to;

    // Row is nondeterministic - row expression is TRUE
    bool nondet=false;

    const namespacet &ns;

    explicit row_valuet(const namespacet &ns):ns(ns) {}

    exprt get_row_expr(const vart &templ_expr) const;

    bool add_points_to(const exprt &dest);
    bool set_nondet();

    void clear();
  };

  // Heap value is a conjunction of rows
  class heap_valuet:public valuet, public std::vector<row_valuet> {};

  // Initialize value and domain
  virtual void initialize(valuet &value) override;

  std::vector<exprt> get_required_smt_values(size_t row);
  void set_smt_values(std::vector<exprt> got_values, size_t row);

  // Value -> constraints
  exprt to_pre_constraints(valuet &_value);

  void make_not_post_constraints(
    valuet &_value,
    exprt::operandst &cond_exprs);

  // Row -> constraints
  exprt get_row_pre_constraint(
    const rowt &row,
    const row_valuet &row_value) const;

  exprt get_row_post_constraint(const rowt &row, const row_valuet &row_value);

  // Printing
  virtual void output_value(
    std::ostream &out,
    const valuet &value,
    const namespacet &ns) const override;

  virtual void output_domain(
    std::ostream &out,
    const namespacet &ns) const override;

  // Projection
  virtual void
  project_on_vars(valuet &value, const var_sett &vars, exprt &result) override;

  // Conversion of solver value to expression
  static exprt value_to_ptr_exprt(const exprt &expr);

  // Join of values
  virtual void join(valuet &value1, const valuet &value2) override;

  // Restriction to symbolic paths
  void restrict_to_sympath(const symbolic_patht &sympath);
  void undo_restriction();
  void eliminate_sympaths(const std::vector<symbolic_patht> &sympaths);
  void clear_aux_symbols();

protected:
  templatet templ;

  exprt solver_value_op0;
  exprt solver_value_op1;

  void make_template(const var_specst &var_specs, const namespacet &ns);

  void add_template_row(const var_spect &var_spec, const typet &pointed_type);
  void add_template_row_pair(
    const var_spect &var_spec1,
    const var_spect &var_spec2,
    const typet &pointed_type);

  virtual exprt get_current_loop_guard(size_t row) override;

  bool edit_row(const rowt &row, valuet &inv, bool improved);

  // Utility functions
  static int get_symbol_loc(const exprt &expr);
  const exprt get_points_to_dest(
    const exprt &solver_value,
    const exprt &templ_row_expr);
};

#endif // CPROVER_2LS_DOMAINS_HEAP_DOMAIN_H
