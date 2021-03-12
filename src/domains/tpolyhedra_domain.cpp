/*******************************************************************\

Module: Template polyhedra domain

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Template polyhedra domain

#ifdef DEBUG
#include <iostream>
#include <langapi/languages.h>
#endif

#include <util/find_symbols.h>
#include <util/simplify_expr.h>

#include "tpolyhedra_domain.h"
#include "strategy_solver_binsearch.h"
#include "strategy_solver_binsearch2.h"
#include "strategy_solver_binsearch3.h"
#include "util.h"
#include "domain.h"

#define SYMB_BOUND_VAR "symb_bound#"

#define ENABLE_HEURISTICS

void tpolyhedra_domaint::initialize_value(domaint::valuet &value)
{
#if 0
  if(templ.size()==0)
    return domaint::initialize(value);
#endif

  auto &v=dynamic_cast<templ_valuet &>(value);
  v.resize(templ.size());
  for(std::size_t row=0; row<templ.size(); row++)
  {
    if(templ[row].guards.kind==guardst::IN)
      v[row]=true_exprt(); // marker for oo
    else
      v[row]=false_exprt(); // marker for -oo
  }
}

bool tpolyhedra_domaint::edit_row(const rowt &row, valuet &_inv, bool improved)
{
  auto &inv=dynamic_cast<templ_valuet &>(_inv);
  inv[row]=simplify_const(smt_model_values[0]);
  return true;
}

void tpolyhedra_domaint::join(
  domaint::valuet &value1,
  const domaint::valuet &value2)
{
#if 0
  if(templ.size()==0)
    return domaint::join(value1, value2);
#endif

  auto &v1=dynamic_cast<templ_valuet &>(value1);
  auto &v2=dynamic_cast<const templ_valuet &>(value2);
  assert(v1.size()==templ.size());
  assert(v1.size()==v2.size());
  for(std::size_t row=0; row<templ.size(); ++row)
  {
    if(v1[row].is_inf() || v2[row].is_inf())
      v1[row]=true_exprt();
    else if(v1[row].is_neg_inf())
      v1[row]=v2[row];
    else if(!v2[row].is_neg_inf())
    {
      if(less_than(v1[row], v2[row]))
        v1[row]=v2[row];
    }
  }
}

tpolyhedra_domaint::row_valuet tpolyhedra_domaint::between(
  const row_valuet &lower, const row_valuet &upper)
{
  if(lower.type()==upper.type() &&
     (lower.type().id()==ID_signedbv || lower.type().id()==ID_unsignedbv))
  {
    typet type=lower.type();
    mp_integer vlower, vupper;
    to_integer(lower, vlower);
    to_integer(upper, vupper);
    assert(vupper>=vlower);
    if(vlower+1==vupper)
      return row_valuet(from_integer(vlower, lower.type())); // floor

#ifdef ENABLE_HEURISTICS
    // heuristics
    if(type.id()==ID_unsignedbv)
    {
      mp_integer vlargest=to_unsignedbv_type(type).largest();
      if(vlower==mp_integer(0) && vupper==vlargest)
        return row_valuet(from_integer(mp_integer(1), type));
      if(vlower==mp_integer(1) && vupper==vlargest)
        return row_valuet(from_integer(mp_integer(vupper-1), type));
      if(vlower==mp_integer(1) && vupper==vlargest-1)
        return row_valuet(from_integer(mp_integer(2), type));
      if(vlower<mp_integer(128) && vupper==vlargest)
        return row_valuet(from_integer(vlargest-1, type));
      if(vlower<mp_integer(128) && vupper==vlargest-1)
        return row_valuet(from_integer(mp_integer(255), type));
    }
    if(type.id()==ID_signedbv)
    {
      mp_integer vlargest=to_signedbv_type(type).largest();
      if(vlower==-vlargest && vupper==vlargest)
        return row_valuet(from_integer(mp_integer(0), type));
      if(vlower==mp_integer(1) && vupper==vlargest)
        return row_valuet(from_integer(mp_integer(2), type));
      if(vlower==mp_integer(-1) && vupper==vlargest)
        return row_valuet(from_integer(mp_integer(0), type));
      if(vlower==mp_integer(0) &&  vupper==vlargest)
        return row_valuet(from_integer(mp_integer(vupper-1), type));
      if(vlower==-(vlargest/2) && vupper==vlargest)
        return row_valuet(from_integer(mp_integer(vlargest/2+1), type));
      if(vlower==vlargest/2+1 && vupper==vlargest)
        return row_valuet(from_integer(mp_integer(vlargest/2+2), type));
      if(vlower==mp_integer(0) && vupper==vlargest-1)
        return row_valuet(from_integer(mp_integer(1), type));
      if(vlower<mp_integer(128) && vupper==vlargest)
        return row_valuet(from_integer(vlargest-1, type));
      if(vlower<mp_integer(128) && vupper==vlargest-1)
        return row_valuet(from_integer(mp_integer(255), type));
      if(vlower<mp_integer(-128) && vupper==mp_integer(255))
        return row_valuet(from_integer(mp_integer(-255), type));
    }
#endif

    return row_valuet(from_integer((vupper+vlower)/2, type));
  }
  if(lower.type().id()==ID_floatbv && upper.type().id()==ID_floatbv)
  {
    ieee_floatt vlower(to_constant_expr(lower));
    ieee_floatt vupper(to_constant_expr(upper));
    if(vlower.get_sign()==vupper.get_sign())
    {
      mp_integer plower=vlower.pack(); // compute "median" float number
      mp_integer pupper=vupper.pack();
#if 0
      assert(pupper>=plower);
#endif
      ieee_floatt res(to_floatbv_type(lower.type()));
      res.unpack((plower+pupper)/2); // ...by computing integer mean
      return row_valuet(res.to_expr());
    }
    ieee_floatt res(to_floatbv_type(lower.type()));
    res.make_zero();
    return row_valuet(res.to_expr());
  }
  assert(false); // types do not match or are not supported
}

bool tpolyhedra_domaint::less_than(const row_valuet &v1, const row_valuet &v2)
{
  if(v1.type()==v2.type() &&
     (v1.type().id()==ID_signedbv || v1.type().id()==ID_unsignedbv))
  {
    mp_integer vv1, vv2;
    to_integer(v1, vv1);
    to_integer(v2, vv2);
    return vv1<vv2;
  }
  if(v1.type().id()==ID_floatbv && v2.type().id()==ID_floatbv)
  {
    ieee_floatt vv1(to_constant_expr(v1));
    ieee_floatt vv2(to_constant_expr(v2));
    return vv1<vv2;
  }
  assert(false); // types do not match or are not supported
}

/// generates symbolic value symbol
symbol_exprt tpolyhedra_domaint::get_row_symb_value(const rowt &row)
{
  assert(row<templ.size());
  auto &row_expr=dynamic_cast<template_row_exprt &>(*templ[row].expr);
  return symbol_exprt(
    SYMB_BOUND_VAR+std::to_string(domain_number)+"$"+std::to_string(row),
    row_expr.type());
}

/// pre_guard==> (row_expr<=symb_value)
exprt tpolyhedra_domaint::get_row_symb_pre_constraint(
  const rowt &row,
  const row_valuet &row_value)
{
  assert(row<templ.size());
  const template_rowt &templ_row=templ[row];
  auto &templ_row_expr=dynamic_cast<template_row_exprt &>(*templ_row.expr);
  if(templ_row.guards.kind==guardst::OUT ||
     templ_row.guards.kind==guardst::OUTL)
    return true_exprt();
  return implies_exprt(
    templ_row.guards.pre_guard,  // REMARK: and_expr==> loop15 regression
    binary_relation_exprt(templ_row_expr, ID_le, get_row_symb_value(row)));
}

/// post_guard && (row_expr >= row_symb_value)  (!!!)
exprt tpolyhedra_domaint::get_row_symb_post_constraint(const rowt &row)
{
  assert(row<templ.size());
  const template_rowt &templ_row=templ[row];
  auto &templ_row_expr=dynamic_cast<template_row_exprt &>(*templ_row.expr);
  if(templ_row.guards.kind==guardst::IN)
    return true_exprt();
  exprt c=and_exprt(
    templ_row.guards.post_guard,
    binary_relation_exprt(templ_row_expr, ID_ge, get_row_symb_value(row)));
  rename(c);
  c=and_exprt(
    c, not_exprt(equal_exprt(get_row_symb_value(row), templ_row_expr)));
  return and_exprt(templ_row.guards.aux_expr, c);
}

/// pre_guard==> (row_expr<=symb_row_value)
exprt tpolyhedra_domaint::to_symb_pre_constraints(const templ_valuet &value)
{
  assert(value.size()==templ.size());
  exprt::operandst c;
  for(std::size_t row=0; row<templ.size(); ++row)
  {
    c.push_back(get_row_symb_pre_constraint(row, value[row]));
  }
  return conjunction(c);
}

/// pre_guard==> (row_expr<=symb_row_value)
exprt tpolyhedra_domaint::to_symb_pre_constraints(
  const templ_valuet &value,
  const std::set<rowt> &symb_rows)
{
  assert(value.size()==templ.size());
  exprt::operandst c;
  for(std::size_t row=0; row<templ.size(); ++row)
  {
    if(symb_rows.find(row)!=symb_rows.end())
      c.push_back(get_row_symb_pre_constraint(row, value[row]));
    else
      c.push_back(get_row_pre_constraint(row, value));
  }
  return conjunction(c);
}

/// /\_i post_guard==> (row_expr >= symb_row_value)
exprt tpolyhedra_domaint::to_symb_post_constraints(
  const std::set<rowt> &symb_rows)
{
  exprt::operandst c;
  for(const auto &row : symb_rows)
  {
    c.push_back(get_row_symb_post_constraint(row));
  }
  return conjunction(c);
}

/// row_value_value<=symb_row
exprt tpolyhedra_domaint::get_row_symb_value_constraint(
  const rowt &row,
  const row_valuet &row_value,
  bool geq)
{
  if(row_value.is_neg_inf())
    return false_exprt();
  if(row_value.is_inf())
    return true_exprt();
  exprt c=binary_relation_exprt(
    get_row_symb_value(row),
    geq ? ID_ge : ID_le,
    row_value);
  return c;
}

tpolyhedra_domaint::row_valuet tpolyhedra_domaint::get_max_row_value(
  const tpolyhedra_domaint::rowt &row)
{
  const template_rowt &templ_row=templ[row];
  auto &templ_row_expr=dynamic_cast<template_row_exprt &>(*templ_row.expr);
  if(templ_row_expr.type().id()==ID_signedbv)
  {
    return row_valuet(to_signedbv_type(templ_row_expr.type()).largest_expr());
  }
  if(templ_row_expr.type().id()==ID_unsignedbv)
  {
    return row_valuet(to_unsignedbv_type(templ_row_expr.type()).largest_expr());
  }
  if(templ_row_expr.type().id()==ID_floatbv)
  {
    ieee_floatt max(to_floatbv_type(templ_row_expr.type()));
    max.make_fltmax();
    return row_valuet(max.to_expr());
  }
  assert(false); // type not supported
}

tpolyhedra_domaint::row_valuet tpolyhedra_domaint::get_min_row_value(
  const tpolyhedra_domaint::rowt &row)
{
  const template_rowt &templ_row=templ[row];
  auto &templ_row_expr=dynamic_cast<template_row_exprt &>(*templ_row.expr);
  if(templ_row_expr.type().id()==ID_signedbv)
  {
    return row_valuet(to_signedbv_type(templ_row_expr.type()).smallest_expr());
  }
  if(templ_row_expr.type().id()==ID_unsignedbv)
  {
    return row_valuet(
      to_unsignedbv_type(templ_row_expr.type()).smallest_expr());
  }
  if(templ_row_expr.type().id()==ID_floatbv)
  {
    ieee_floatt min(to_floatbv_type(templ_row_expr.type()));
    min.make_fltmin();
    return row_valuet(min.to_expr());
  }
  assert(false); // type not supported
}

void tpolyhedra_domaint::output_value(
  std::ostream &out,
  const domaint::valuet &value,
  const namespacet &ns) const
{
  auto &v=dynamic_cast<const templ_valuet &>(value);
  for(std::size_t row=0; row<templ.size(); ++row)
  {
    auto &templ_row_expr=dynamic_cast<template_row_exprt &>(*templ[row].expr);
    templ[row].guards.output(out, ns);
    out << "( " << from_expr(ns, "", templ_row_expr) << "<=";
    if(v[row].is_inf())
      out << "-oo";
    else if(v[row].is_neg_inf())
      out << "oo";
    else
      out << from_expr(ns, "", v[row]);
    out << " )" << std::endl;
  }
}

/// add row suffix to non-symbolic-bound variables in expression (required for
/// strategy iteration (binsearch3))
void tpolyhedra_domaint::rename_for_row(exprt &expr, const rowt &row)
{
  if(row==0)
    return; // do not rename
  if(expr.id()==ID_symbol || expr.id()==ID_nondet_symbol)
  {
    const std::string &old_id=expr.get_string(ID_identifier);
    if(old_id.find(SYMB_BOUND_VAR)==std::string::npos)
    {
      irep_idt id=old_id+"_"+std::to_string(row);
      expr.set(ID_identifier, id);
    }
  }
  for(std::size_t i=0; i<expr.operands().size(); ++i)
    rename_for_row(expr.operands()[i], row);
}

tpolyhedra_domaint::template_rowt &tpolyhedra_domaint::add_template_row(
  const exprt &expr,
  const guardst &guards)
{
  templ.push_back(template_rowt());
  template_rowt &templ_row=templ.back();
  templ_row.expr=std::unique_ptr<template_row_exprt>(
    new template_row_exprt(expr));
  extend_expr_types(dynamic_cast<exprt &>(*templ_row.expr));
  templ_row.guards=guards;
  return templ_row;
}

/// +-x<=c
void tpolyhedra_domaint::add_interval_template(
  const var_specst &var_specs,
  const namespacet &ns)
{
  unsigned size=2*var_specs.size();
  templ.reserve(templ.size()+size);

  for(const auto &v : var_specs)
  {
    if(v.guards.kind==guardst::IN)
      continue;
    if(v.var.type().id()==ID_pointer)
      continue;

    // x
    add_template_row(v.var, v.guards);

    // -x
    add_template_row(unary_minus_exprt(v.var, v.var.type()), v.guards);
  }
}

/// x+-y<=c
void tpolyhedra_domaint::add_difference_template(
  const var_specst &var_specs,
  const namespacet &ns)
{
  std::size_t size=var_specs.size()*(var_specs.size()-1);
  templ.reserve(templ.size()+size);

  for(var_specst::const_iterator v1=var_specs.begin();
      v1!=var_specs.end(); ++v1)
  {
    if(v1->var.type().id()==ID_pointer)
      continue;
    if(v1->var.id()==ID_and)
      continue;
    var_specst::const_iterator v2=v1;
    ++v2;
    for(; v2!=var_specs.end(); ++v2)
    {
      if(v2->var.id()==ID_and)
        continue;

      // Check if both vars are dynamic objects allocated by the same malloc.
      // In such case, do not add the template row, since only one of those is
      // always allocated and the combined guard would never hold.
      if(v1->var.id()==ID_symbol && v2->var.id()==ID_symbol)
      {
        int v1_index=get_dynobj_line(to_symbol_expr(v1->var).get_identifier());
        int v2_index=get_dynobj_line(to_symbol_expr(v2->var).get_identifier());
        if(v1_index>=0 && v2_index>=0 && v1_index==v2_index)
        {
          std::string v1_inst=get_dynobj_instance(
            to_symbol_expr(v1->var).get_identifier());
          std::string v2_inst=get_dynobj_instance(
            to_symbol_expr(v2->var).get_identifier());
          if(v1_inst!="" && v2_inst!="" && v1_inst!=v2_inst)
            continue;
        }
      }

      guardst guards=guardst::merge_and_guards(v1->guards, v2->guards, ns);
      if(guards.kind==guardst::IN)
        continue;
      if(guards.kind==guardst::LOOP &&
         v1->guards.pre_guard!=v2->guards.pre_guard)
        continue; // TEST: we need better heuristics
      if(v2->var.type().id()==ID_pointer)
        continue;
      if(guards.post_guard.is_false())
        continue;

      // x1-x2
      add_template_row(minus_exprt(v1->var, v2->var), guards);

      // x2-x1
      add_template_row(minus_exprt(v2->var, v1->var), guards);
    }
  }
}

/// +-x^2<=c
void tpolyhedra_domaint::add_quadratic_template(
  const var_specst &var_specs,
  const namespacet &ns)
{
  unsigned size=2*var_specs.size();
  templ.reserve(templ.size()+size);

  for(const auto v : var_specs)
  {
    if(v.guards.kind==guardst::IN)
      continue;

    // x
    add_template_row(mult_exprt(v.var, v.var), v.guards);

    // -x
    add_template_row(
      unary_minus_exprt(mult_exprt(v.var, v.var), v.var.type()), v.guards);
  }
}

/// x+y<=c, -x-y<=c
void tpolyhedra_domaint::add_sum_template(
  const var_specst &var_specs,
  const namespacet &ns)
{
  unsigned size=var_specs.size()*(var_specs.size()-1);
  templ.reserve(templ.size()+size);

  for(var_specst::const_iterator v1=var_specs.begin();
      v1!=var_specs.end(); ++v1)
  {
    var_specst::const_iterator v2=v1; ++v2;
    for(; v2!=var_specs.end(); ++v2)
    {
      auto guards=guardst::merge_and_guards(v1->guards, v2->guards, ns);
      if(guards.kind==guardst::IN)
        continue;
      if(guards.kind==guardst::LOOP &&
         v1->guards.pre_guard!=v2->guards.pre_guard)
        continue; // TEST: we need better heuristics

      // -x1-x2
      add_template_row(
        minus_exprt(unary_minus_exprt(v1->var, v1->var.type()), v2->var),
        guards);

      // x1+x2
      add_template_row(plus_exprt(v1->var, v2->var), guards);
    }
  }
}

/// Choose a correct solver based on the used strategy
std::unique_ptr<strategy_solver_baset> tpolyhedra_domaint::new_strategy_solver(
  incremental_solvert &solver,
  const local_SSAt &SSA,
  message_handlert &message_handler)
{
  switch(strategy)
  {
  case ENUMERATION:
    return simple_domaint::new_strategy_solver(solver, SSA, message_handler);
  case BINSEARCH:
    return std::unique_ptr<strategy_solver_baset>(
      new strategy_solver_binsearcht(*this, solver, SSA, message_handler));
  case BINSEARCH2:
    return std::unique_ptr<strategy_solver_baset>(
      new strategy_solver_binsearch2t(*this, solver, SSA, message_handler));
  case BINSEARCH3:
    return std::unique_ptr<strategy_solver_baset>(
      new strategy_solver_binsearch3t(*this, solver, SSA, message_handler));
  }
}

void tpolyhedra_domaint::template_row_exprt::output(
  std::ostream &out,
  const namespacet &ns) const
{
  out << from_expr(ns, "", *this) << "<=CONST" << std::endl;
}
