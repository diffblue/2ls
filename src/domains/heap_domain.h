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

#include "simple_domain.h"
#include "template_generator_base.h"
#include <ssa/ssa_inliner.h>

class heap_domaint:public simple_domaint
{
public:
  heap_domaint(
    unsigned int _domain_number,
    replace_mapt &_renaming_map,
    const var_specst &var_specs,
    const local_SSAt &SSA):
    simple_domaint(_domain_number, _renaming_map, SSA.ns)
  {
    make_template(var_specs, ns);
  }

  /// Heap template row describes a set of pointer expressions
  struct template_row_exprt:public simple_domaint::template_row_exprt
  {
    var_listt pointers;

    explicit template_row_exprt(var_listt pointers):
      pointers(std::move(pointers)) {}

    std::vector<exprt> get_row_exprs() override { return {pointers}; }

    void output(std::ostream &out, const namespacet &ns) const override;
  };

  /// Value of a heap template row describes a may point-to relation for the row
  /// pointers.
  struct row_valuet
  {
    // Single points-to relation for a vector of pointer expressions.
    // For each pointer, it contains a single pointed object (or NULL).
    // The order is important - it should match the order of pointers in
    // the template row.
    typedef std::vector<exprt> points_to_relt;

    // May point-to relation: it is a set of possible points-to relations.
    std::set<points_to_relt> may_point_to;

    // Row is nondeterministic - row expression is TRUE
    bool nondet=false;

    explicit row_valuet(const namespacet &ns):ns(ns) {}

    exprt get_row_expr(const template_row_exprt &templ_row_expr) const;

    bool add_points_to(const points_to_relt &destinations);
    bool set_nondet();

  protected:
    const namespacet &ns;
  };

  // Heap value is a conjunction of rows
  struct heap_valuet:simple_domaint::valuet, std::vector<row_valuet>
  {
    exprt get_row_expr(rowt row, const template_rowt &templ_row) const override
    {
      auto &templ_row_expr=dynamic_cast<template_row_exprt &>(*templ_row.expr);
      return (*this)[row].get_row_expr(templ_row_expr);
    }
  };

  // Initialize value and domain
  void initialize_value(domaint::valuet &value) override;

  // Handle row edit - join the model obtained from SMT with inv
  bool edit_row(const rowt &row, valuet &inv, bool improved) override;

  // Conversion of solver value to expression
  static exprt value_to_ptr_exprt(const exprt &expr);

protected:
  void make_template(const var_specst &var_specs, const namespacet &ns);
  void add_template_row(var_listt pointers, const guardst &guards);

  // Utility functions
  const exprt get_points_to_dest(
    const exprt &solver_value,
    const exprt &templ_row_expr);
};

#endif // CPROVER_2LS_DOMAINS_HEAP_DOMAIN_H
