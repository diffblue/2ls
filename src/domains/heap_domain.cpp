/*******************************************************************\

Module: Abstract domain for representing heap

Author: Viktor Malik

\*******************************************************************/

/// \file
/// Abstract domain for representing heap

#include "heap_domain.h"
#include <algorithm>
#include <memory>
#include <ssa/address_canonizer.h>
#include <util/mathematical_types.h>
#include <util/pointer_expr.h>

/// Initialize abstract value. Clears value with empty value rows corresponding
/// to template.
void heap_domaint::initialize_value(domaint::valuet &value)
{
  auto &heap_val=dynamic_cast<heap_valuet &>(value);
  for(int i=0; i<templ.size(); i++)
    heap_val.emplace_back(row_valuet(ns));
}

/// Create domain template for given set of variables. Template contains a row
/// for each pointer-typed variable and  field of a dynamic object.
void heap_domaint::make_template(
  const var_specst &var_specs,
  const namespacet &ns)
{
  unsigned long size=var_specs.size();
  templ.clear();
  templ.reserve(size);

  for(const var_spect &v : var_specs)
  {
    if(v.guards.kind==guardst::IN)
      continue;

    // Create template row for each pointer
    const vart &var=v.var;
    if(var.type().id()==ID_pointer)
    {
      add_template_row({var}, v.guards);

      if(var.id()==ID_symbol &&
         id2string(to_symbol_expr(var).get_identifier()).find(
           "__CPROVER_deallocated")!=std::string::npos)
      {
        // Create template row for a pair of pointers for __CPROVER_deallocated
        // with each pointer.
        for(const var_spect &v_other : var_specs)
        {
          if(!(v_other.var.type().id()==ID_pointer &&
               v_other.guards.kind==guardst::LOOP &&
               v_other.guards.pre_guard==v.guards.pre_guard))
          {
            // Pointers must be in the same loop
            continue;
          }

          if(v_other.var.id()==ID_symbol &&
             id2string(to_symbol_expr(v_other.var).get_identifier()).find(
               "__CPROVER_")!=std::string::npos)
          {
            // Other pointer must not be CPROVER-specific
            continue;
          }

          add_template_row({var, v_other.var}, v.guards);
        }
      }
    }
  }
}

/// Add a template row.
/// \param guards: Variable specification
/// \param pointers: Pointed type
void heap_domaint::add_template_row(
  var_listt pointers,
  const guardst &guards)
{
  templ.push_back(template_rowt());
  template_rowt &templ_row=templ.back();
  templ_row.expr=std::unique_ptr<template_row_exprt>(
    new template_row_exprt(std::move(pointers)));
  templ_row.guards=guards;
}

/// Converts a constant returned from the solver to the corresponding
/// expression.
exprt heap_domaint::value_to_ptr_exprt(const exprt &expr)
{
  if(expr.id()==ID_annotated_pointer_constant)
  {
    const unary_exprt &constant=to_unary_expr(expr);
    const std::string value=id2string(
      to_annotated_pointer_constant_expr(expr).get_value());
    if(value.substr(value.size()/2).find_first_not_of('0')!=std::string::npos)
      return plus_exprt(constant.op(), make_zero(integer_typet()));
    else
      return constant.op();
  }

  return expr;
}

/// \param ptr_expr: Pointer expression (variable)
/// \param ptr_value: Value (object or address) of the pointer
/// \return Equality between pointer and its value with correct types
const exprt ptr_equality(
  const exprt &ptr_expr,
  const exprt &ptr_value,
  const namespacet &ns)
{
  exprt value;
  if(ptr_expr.type()==ptr_value.type())
    value=ptr_value;
  else if(ns.follow(ptr_expr.type().subtype())==ns.follow(ptr_value.type()))
    value=address_of_exprt(ptr_value);
  else
  {
    value=typecast_exprt(
      address_of_exprt(ptr_value),
      ns.follow(ptr_expr.type()));
  }
  return equal_exprt(ptr_expr, value);
}

/// Row value is a disjuction of equalities between templ_expr and addresses of
/// dynamic objects from the points_to set.
/// \param templ_row_expr: Template expression
/// \param rename_templ_expr: Unused
/// \return Formula corresponding to the template row
exprt heap_domaint::row_valuet::get_row_expr(
  const template_row_exprt &templ_row_expr) const
{
  if(nondet)
    return true_exprt();
  if(may_point_to.empty())
    return false_exprt();

  // Row expression is a disjunction of possible points-to relations.
  exprt::operandst result;
  for(auto &points_to : may_point_to)
  {
    // Single points-to relation is a conjunction of pointer equalities for
    // individual template row expressions and their corresponding targets.
    exprt::operandst c;
    for(unsigned i=0; i<templ_row_expr.pointers.size(); i++)
    {
      c.push_back(ptr_equality(templ_row_expr.pointers[i], points_to[i], ns));
    }
    result.push_back(conjunction(c));
  }
  return disjunction(result);
}

/// Add new expression to the set of pointed objects.
/// In case it is already there, set row to nondet.
bool heap_domaint::row_valuet::add_points_to(
  const points_to_relt &destinations)
{
  if(may_point_to.find(destinations)==may_point_to.end())
  {
    may_point_to.insert(destinations);
    return true;
  }

  return set_nondet();
}

bool heap_domaint::row_valuet::set_nondet()
{
  bool changed=!nondet;
  nondet=true;
  return changed;
}

bool heap_domaint::edit_row(const rowt &row, valuet &_inv, bool improved)
{
  auto &value_row=dynamic_cast<heap_valuet &>(_inv)[row];
  auto &templ_row_pointers=
    dynamic_cast<template_row_exprt &>(*templ[row].expr).pointers;

  row_valuet::points_to_relt points_to_destinations;
  for(unsigned i=0; i<templ_row_pointers.size(); i++)
  {
    exprt points_to_dest=get_points_to_dest(
      smt_model_values[i], templ_row_pointers[i]);

    if(points_to_dest.is_nil())
    {
      if(value_row.set_nondet())
        improved=true;
      return improved;
    }

    points_to_destinations.push_back(points_to_dest);
  }

  if(value_row.add_points_to(points_to_destinations))
    improved=true;

  return improved;
}

/// Get an address where the given pointer points to in the current solver
/// iteration. Returns nil_exprt if the value of the pointer is nondet.
const exprt heap_domaint::get_points_to_dest(
  const exprt &solver_value,
  const exprt &templ_row_expr)
{
  // Value from the solver must be converted into an expression
  exprt ptr_value=value_to_ptr_exprt(solver_value);
  if(ptr_value.id()==ID_typecast)
    ptr_value=to_typecast_expr(ptr_value).op();

  if((ptr_value.id()==ID_constant &&
      to_constant_expr(ptr_value).get_value()==ID_NULL) ||
     ptr_value.id()==ID_symbol)
  {
    // Add equality p == NULL or p == symbol
    return ptr_value;
  }
  else if(ptr_value.id()==ID_address_of)
  {
    // Template row pointer points to the heap (p = &obj)
    assert(ptr_value.id()==ID_address_of);
    exprt obj=to_address_of_expr(ptr_value).object();
    if(obj.id()==ID_member)
    {
      // &(X.field) where field has offset 0 is equal to &X
      auto &member=to_member_expr(obj);
      auto field=member.get_component_name();
      auto struct_type=ns.follow(member.compound().type());
      if(struct_type.id()==ID_struct &&
         to_struct_type(struct_type).component_number(field)==0)
      {
        obj=member.compound();
      }
    }
    if(obj.id()!=ID_symbol)
    {
      // If solver did not return address of a symbol, it is considered
      // as nondet value.
      return nil_exprt();
    }

    symbol_exprt symbol_obj=to_symbol_expr(obj);

    if(symbol_obj.type()!=templ_row_expr.type() &&
       ns.follow(templ_row_expr.type().subtype())!=ns.follow(symbol_obj.type()))
    {
      if(!is_cprover_symbol(templ_row_expr))
      {
        // If types disagree, it's a nondet (solver assigned random value)
        return nil_exprt();
      }
    }

    // Add equality p == &obj
    return std::move(symbol_obj);
  }
  else
    return nil_exprt();
}

void heap_domaint::template_row_exprt::output(
  std::ostream &out,
  const namespacet &ns) const
{
  for(auto &ptr : pointers)
  {
    out << from_expr(ns, "", ptr) << " --points to--> ADDR" << std::endl;
  }
}
