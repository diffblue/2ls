/*******************************************************************\

Module: Equalities/Disequalities domain

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Equalities/Disequalities domain

#ifdef DEBUG
#include <iostream>
#include <langapi/languages.h>
#endif

#include <util/find_symbols.h>
#include <util/arith_tools.h>
#include <util/ieee_float.h>
#include <util/simplify_expr.h>

#include "equality_domain.h"
#include "util.h"

exprt equality_domaint::equ_valuet::get_row_expr(
  rowt row,
  const simple_domaint::template_rowt &templ_row) const
{
  auto &templ_row_expr=dynamic_cast<template_row_exprt &>(*templ_row.expr);
  return equal_exprt(templ_row_expr.first, templ_row_expr.second);
}

void equality_domaint::initialize_value(domaint::valuet &value)
{
  auto &v=dynamic_cast<equ_valuet &>(value);
  v.equs.clear();
  v.disequs.clear();
}

void equality_domaint::init_value_solver_iteration(domaint::valuet &value)
{
  e_it=todo_equs.begin();
  unsatisfiable=false;
}

bool equality_domaint::has_something_to_solve()
{
  if(e_it!=todo_equs.end())
  {
    check_dis=false;
    return true;
  }
  if(todo_disequs.begin()!=todo_disequs.end())
  {
    e_it=todo_disequs.begin();
    check_dis=true;
    return true;
  }
  return false;
}

bool equality_domaint::edit_row(const rowt &row, valuet &inv, bool improved)
{
  if(!check_dis)
    todo_disequs.insert(*e_it);
  return true;
}

void equality_domaint::finalize_solver_iteration()
{
  if(check_dis)
    todo_disequs.erase(e_it);
  else
    todo_equs.erase(e_it);
}

exprt equality_domaint::to_pre_constraints(const valuet &value)
{
  return get_row_pre_constraint(*e_it, value);
}

void equality_domaint::make_not_post_constraints(
  const valuet &value,
  exprt::operandst &cond_exprs)
{
  cond_exprs.clear();
  if(templ[*e_it].guards.kind==guardst::IN)
    cond_exprs.push_back(true_exprt());
  else
    cond_exprs.push_back(get_row_post_constraint(*e_it, value));
}

exprt equality_domaint::get_row_value_constraint(
  rowt row,
  const simple_domaint::valuet &value)
{
  exprt row_value_expr=value.get_row_expr(row, templ[row]);
  if(check_dis)
    row_value_expr=not_exprt(row_value_expr);
  return row_value_expr;
}

bool equality_domaint::handle_unsat(valuet &value, bool improved)
{
  auto &inv=dynamic_cast<equality_domaint::equ_valuet &>(value);
  if(check_dis)
    set_disequal(*e_it, inv);
  unsatisfiable=true;
  return true;
}

exprt equality_domaint::get_permanent_expr(valuet &value)
{
  auto &inv=dynamic_cast<equality_domaint::equ_valuet &>(value);
  if(unsatisfiable)
  {
    if(!check_dis)
    {
      set_equal(*e_it, inv);

      // due to transitivity, we have to recheck equalities
      //   that did not hold
      todo_equs.insert(todo_disequs.begin(), todo_disequs.end());
      todo_disequs.clear();
    }
    return to_pre_constraints(value);
  }
  return true_exprt();
}

void equality_domaint::project_on_vars(
  domaint::valuet &value,
  const var_sett &vars,
  exprt &result)
{
#if 0
  if(templ.size()==0)
    return domaint::project_on_vars(value, vars, result);
#endif

  auto &v=dynamic_cast<equ_valuet &>(value);

  exprt::operandst c;
  for(rowt row=0; row<templ.size(); row++)
  {
    auto &templ_row_expr=dynamic_cast<template_row_exprt &>(*templ[row].expr);

#if 0
    std::cout << vv.second << std::endl;
#endif
    if(vars.find(templ_row_expr.first)==vars.end() ||
       (vars.find(templ_row_expr.second)==vars.end() &&
        !(templ_row_expr.second.id()==ID_constant &&
          to_constant_expr(templ_row_expr.second).get_value()=="NULL")))
      continue;

    if(v.equs.same_set(templ_row_expr.first, templ_row_expr.second))
    {
      check_dis=false;
      if(templ[row].guards.kind==guardst::LOOP)
        c.push_back(get_row_pre_constraint(row, v));
      else
        c.push_back(get_row_value_constraint(row, v));
    }
  }

  for(auto &disequ : v.disequs)
  {
    auto &templ_row_expr=
      dynamic_cast<template_row_exprt &>(*templ[disequ].expr);

    if(vars.find(templ_row_expr.first)==vars.end() ||
       (vars.find(templ_row_expr.second)==vars.end() &&
        !(templ_row_expr.second.id()==ID_constant &&
          to_constant_expr(templ_row_expr.second).get_value()=="NULL")))
      continue;

    check_dis=true;
    if(templ[disequ].guards.kind==guardst::LOOP)
      c.push_back(get_row_pre_constraint(disequ, v));
    else
      c.push_back(get_row_value_constraint(disequ, v));
  }
  result=conjunction(c);
}

void equality_domaint::set_equal(
  unsigned index, equ_valuet &value)
{
  assert(index<templ.size());
  auto &templ_row_expr=dynamic_cast<template_row_exprt &>(*templ[index].expr);
  value.set_equal(templ_row_expr.first, templ_row_expr.second);
}

void equality_domaint::set_disequal(
  unsigned index, equ_valuet &value)
{
  assert(index<templ.size());
  value.set_disequal(index);
}

void equality_domaint::output_value(
  std::ostream &out,
  const domaint::valuet &value,
  const namespacet &ns) const
{
  auto &_v=dynamic_cast<const equ_valuet &>(value);
  equ_valuet v=_v;

  for(unsigned index=0; index<templ.size(); index++)
  {
    auto &templ_row_expr=dynamic_cast<template_row_exprt &>(*templ[index].expr);
    if(v.equs.same_set(templ_row_expr.first, templ_row_expr.second))
    {
      out << from_expr(ns, "", templ_row_expr.first) << "=="
          << from_expr(ns, "", templ_row_expr.second) << std::endl;
    }
  }

  for(index_sett::const_iterator it=v.disequs.begin();
      it!=v.disequs.end(); it++)
  {
    auto &templ_row_expr=dynamic_cast<template_row_exprt &>(*templ[*it].expr);
    out << from_expr(ns, "", templ_row_expr.first) << "!="
        << from_expr(ns, "", templ_row_expr.second) << std::endl;
  }
}

bool equality_domaint::adapt_types(exprt &v1, exprt &v2)
{
  // signed, unsigned integers
  if((v1.type().id()==ID_signedbv || v1.type().id()==ID_unsignedbv) &&
     (v2.type().id()==ID_signedbv || v2.type().id()==ID_unsignedbv))
  {
    unsigned size1=0, size2=0;
    if(v1.type().id()==ID_signedbv)
      size1=to_signedbv_type(v1.type()).get_width();
    if(v1.type().id()==ID_unsignedbv)
      size1=to_unsignedbv_type(v1.type()).get_width();
    if(v2.type().id()==ID_signedbv)
      size2=to_signedbv_type(v2.type()).get_width();
    if(v2.type().id()==ID_unsignedbv)
      size2=to_unsignedbv_type(v2.type()).get_width();

    if(v1.type().id()==v2.type().id())
    {
      if(size1==size2)
        return true;

      typet new_type=v1.type();
      if(new_type.id()==ID_signedbv)
        to_signedbv_type(new_type).set_width(std::max(size1, size2));
      else // if(new_type.id()==ID_unsignedbv)
        to_unsignedbv_type(new_type).set_width(std::max(size1, size2));

      if(size1>size2)
        v2=typecast_exprt(v2, new_type);
      else
        v1=typecast_exprt(v1, new_type);
      return true;
    }

    // types are different
    typet new_type=signedbv_typet(std::max(size1, size2)+1);
    v1=typecast_exprt(v1, new_type);
    v2=typecast_exprt(v2, new_type);
    return true;
  }

  // pointer equality
  if(v1.type().id()==ID_pointer && v2.type().id()==ID_pointer)
  {
    if(to_pointer_type(v1.type()).subtype()==
       to_pointer_type(v2.type()).subtype())
      return true;
    return false;
  }

  if(v1.id()==ID_index || v2.id()==ID_index)
  {
#if 0
    std::cout << "v1: " << v1 << std::endl;
    std::cout << "v2: " << v2 << std::endl;
#endif
    // TODO: implement
    return false;
  }

  return false; // types incompatible
}

void equality_domaint::make_template(
  const var_specst &var_specs,
  const namespacet &ns)
{
  unsigned size=var_specs.size(); // just an estimate
  templ.clear();
  templ.reserve(size);

  for(var_specst::const_iterator v1=var_specs.begin();
      v1!=var_specs.end(); v1++)
  {
    //  NULL pointer checks
    if(v1->var.type().id()==ID_pointer)
    {
      templ.push_back(template_rowt());
      template_rowt &templ_row=templ.back();
      templ_row.expr=std::unique_ptr<template_row_exprt>(
        new template_row_exprt(
          v1->var, null_pointer_exprt(to_pointer_type(v1->var.type()))));
      templ_row.guards=v1->guards;
    }

    var_specst::const_iterator v2=v1; v2++;
    for(; v2!=var_specs.end(); v2++)
    {
      guardst guards=guardst::merge_and_guards(v1->guards, v2->guards, ns);

#if 0
      // TODO: must be done in caller (for preconditions, e.g.)
      if(k==IN)
        continue;
#endif

      exprt vv1=v1->var;
      exprt vv2=v2->var;
      if(!adapt_types(vv1, vv2))
        continue;

      templ.push_back(template_rowt());
      template_rowt &templ_row=templ.back();
      templ_row.expr=std::unique_ptr<template_row_exprt>(
        new template_row_exprt(vv1, vv2));
      templ_row.guards=guards;
    }
  }
}

void equality_domaint::initialize()
{
  get_index_set(todo_equs);
}

void equality_domaint::get_index_set(std::set<unsigned> &indices)
{
  for(unsigned i=0; i<templ.size(); i++)
    indices.insert(i);
}

void equality_domaint::template_row_exprt::output(
  std::ostream &out,
  const namespacet &ns) const
{
  out << from_expr(ns, "", first) << "=!= " << from_expr(ns, "", second)
      << std::endl;
}
