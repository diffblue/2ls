/*******************************************************************\

Module: Predicate abstraction domain

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Predicate abstraction domain

#ifdef DEBUG
#include <iostream>
#endif

#include <util/find_symbols.h>
#include <util/prefix.h>
#include <util/simplify_expr.h>
#include <langapi/languages.h>

#include "predabs_domain.h"
#include "util.h"

#define SYMB_COEFF_VAR "symb_coeff#"
#define COMPLEXITY_COUNTER_PREFIX "__CPROVER_CPLX_CNT_"

void predabs_domaint::initialize_value(domaint::valuet &value)
{
  auto &v=dynamic_cast<templ_valuet &>(value);
  v.resize(templ.size());
  for(std::size_t row=0; row<templ.size(); ++row)
  {
    // start from top (we can only use a gfp solver for this domain)
    v[row]=false_exprt();
  }
}

void predabs_domaint::initialize()
{
  get_row_set(todo_preds);
}


void predabs_domaint::init_value_solver_iteration(domaint::valuet &value)
{
  e_it=todo_preds.begin();
}

bool predabs_domaint::has_something_to_solve()
{
  return (e_it==todo_preds.end());
}

bool predabs_domaint::edit_row(const rowt &row, valuet &inv, bool improved)
{
  todo_notpreds.insert(*e_it);
  return true;
}

void predabs_domaint::finalize_solver_iteration()
{
  todo_preds.erase(e_it);
}

bool predabs_domaint::handle_unsat(valuet &value, bool improved)
{
  dynamic_cast<templ_valuet &>(value).set_row_value(*e_it, true_exprt());
  return true;
}

exprt predabs_domaint::get_permanent_expr(valuet &value)
{
  exprt to_r=to_pre_constraints(value);
  todo_preds.insert(todo_notpreds.begin(), todo_notpreds.end());
  todo_notpreds.clear();
  return to_r;
}

/// /\_all_rows ( pre_guard==> (row_value=> row_expr) )
exprt predabs_domaint::to_pre_constraints(const valuet &value)
{
  exprt c=get_row_pre_constraint(*e_it, value);
  if(c.id()==ID_implies)
  {
    // Pre-constraint is (true => row_expr)
    c=implies_exprt(
      true_exprt(),
      dynamic_cast<template_row_exprt &>(*templ[*e_it].expr));
  }
  return c;
}

predabs_domaint::template_rowt &predabs_domaint::add_template_row(
  const exprt &expr,
  const guardst &guards)
{
  templ.push_back(template_rowt());
  template_rowt &templ_row=templ.back();
  templ_row.expr=std::unique_ptr<template_row_exprt>(
    new template_row_exprt(expr));
  // extend_expr_types(templ_row.expr);
  templ_row.guards=guards;
  return templ_row;
}

void predabs_domaint::get_row_set(std::set<rowt> &rows)
{
  for(std::size_t i=0; i<templ.size(); ++i)
    rows.insert(i);
}

void predabs_domaint::template_row_exprt::output(
  std::ostream &out,
  const namespacet &ns) const
{
  out << "( " << from_expr(ns, "", *this) << ")" << std::endl;
}
