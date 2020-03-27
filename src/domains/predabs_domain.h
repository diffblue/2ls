/*******************************************************************\

Module: Predicate abstraction domain

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Predicate abstraction domain

#ifndef CPROVER_2LS_DOMAINS_PREDABS_DOMAIN_H
#define CPROVER_2LS_DOMAINS_PREDABS_DOMAIN_H

#include <set>

#include <util/std_expr.h>
#include <util/arith_tools.h>
#include <util/ieee_float.h>

#include "simple_domain.h"

class predabs_domaint:public simple_domaint
{
public:
  typedef unsigned rowt;

  struct template_row_exprt:simple_domaint::template_row_exprt, exprt
  {
    explicit template_row_exprt(const exprt &expr):exprt(expr) {}

    std::vector<exprt> get_row_exprs() override { return {*this}; }
    void output(std::ostream &out, const namespacet &ns) const override;
  };

  typedef constant_exprt row_valuet;

  struct templ_valuet:simple_domaint::valuet, std::vector<row_valuet>
  {
    void set_row_value(rowt row, const constant_exprt &value)
    {
      (*this)[row]=value;
    }

    exprt get_row_expr(rowt row, const template_rowt &templ_row) const override
    {
      auto &templ_row_expr=dynamic_cast<template_row_exprt &>(*templ_row.expr);
      // row_value => row_expr
      return implies_exprt((*this)[row], templ_row_expr);
    }
  };

  predabs_domaint(
    unsigned _domain_number,
    replace_mapt &_renaming_map,
    const namespacet &_ns):
    simple_domaint(_domain_number, _renaming_map, _ns) {}

  void initialize() override;

  // initialize value
  void initialize_value(domaint::valuet &value) override;

  void init_value_solver_iteration(domaint::valuet &value) override;

  bool has_something_to_solve() override;

  bool edit_row(const rowt &row, valuet &inv, bool improved) override;

  void finalize_solver_iteration() override;

  exprt to_pre_constraints(const valuet &_value) override;

  bool handle_unsat(valuet &value, bool improved) override;

  exprt get_permanent_expr(valuet &value) override;

  // generating templates
  template_rowt &add_template_row(const exprt &expr, const guardst &guards);

  void get_row_set(std::set<rowt> &rows);

  typedef std::set<unsigned> worklistt;
  worklistt::iterator e_it;
  worklistt todo_preds;
  worklistt todo_notpreds;
};

#endif
