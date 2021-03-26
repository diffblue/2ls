/*******************************************************************\

Module: Linear ranking function domain

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Linear ranking function domain

#ifdef DEBUG
#include <iostream>
#endif

#include <util/find_symbols.h>
#include <util/simplify_expr.h>
#include <langapi/languages.h>
#include <util/cprover_prefix.h>
#include <goto-symex/adjust_float_expressions.h>

#include "linrank_domain.h"
#include "util.h"

#define SYMB_COEFF_VAR "symb_coeff#"

#define EXTEND_TYPES
#define DIFFERENCE_ENCODING

#define COEFF_C_SIZE 10
#define MAX_REFINEMENT 2

void linrank_domaint::initialize_value(domaint::valuet &value)
{
  auto &v=dynamic_cast<templ_valuet &>(value);
  v.resize(templ.size());
  for(unsigned row=0; row<templ.size(); row++)
    v[row].c.push_back(false_exprt());
}

bool linrank_domaint::edit_row(const rowt &row, valuet &inv, bool improved)
{
  auto &rank=dynamic_cast<linrank_domaint::templ_valuet &>(inv);
  exprt rounding_mode=symbol_exprt(
    CPROVER_PREFIX "rounding_mode",
    signedbv_typet(32));

  linrank_domaint::row_valuet symb_values;
  exprt constraint;
  exprt refinement_constraint;

  // generate the new constraint
  constraint=get_row_symb_constraint(
    symb_values, row, refinement_constraint);
  simplify_expr(constraint, ns);

  *inner_solver << equal_exprt(
    rounding_mode, from_integer(mp_integer(0), signedbv_typet(32)));
  *inner_solver << constraint;

  // refinement
  if(!refinement_constraint.is_true())
  {
    inner_solver->new_context();
    *inner_solver << refinement_constraint;
  }

  // solve
  if((*inner_solver)()==decision_proceduret::resultt::D_SATISFIABLE &&
     number_inner_iterations<max_inner_iterations)
  {
    std::vector<exprt> c=symb_values.c;

    // new_row_values will contain the new values for c
    linrank_domaint::row_valuet new_row_values;

    // get the model for all c
    for(const auto &e : c)
    {
      exprt v=inner_solver->solver->get(e);
      new_row_values.c.push_back(v);
    }
    exprt rmv=inner_solver->solver->get(rounding_mode);

    // update the current template
    rank[row]=new_row_values;

    improved=true;
  }
  else
  {
    if(refine())
    {
      improved=true; // refinement possible
    }
    else
    {
      // no ranking function for the current template
      rank[row].set_to_true();
      reset_refinements();
    }
  }

  if(!refinement_constraint.is_true())
    inner_solver->pop_context();

  return improved;
}

exprt linrank_domaint::to_pre_constraints(const valuet &_value)
{
  exprt rounding_mode=symbol_exprt(
    CPROVER_PREFIX "rounding_mode",
    signedbv_typet(32));

  return equal_exprt(
    rounding_mode,
    from_integer(mp_integer(0), signedbv_typet(32)));
}


bool linrank_domaint::handle_unsat(valuet &value, bool improved)
{
  reset_refinements();
  return improved;
}

bool linrank_domaint::refine()
{
  if(refinement_level>=MAX_REFINEMENT)
    return false;
  refinement_level++;
  return true;
}

void linrank_domaint::make_not_post_constraints(
  const valuet &_value,
  exprt::operandst &cond_exprs)
{
  auto &value=dynamic_cast<const templ_valuet &>(_value);
  assert(value.size()==templ.size());
  cond_exprs.resize(value.size());
  strategy_value_exprs.resize(value.size());

  for(unsigned row=0; row<templ.size(); row++)
  {
    auto row_exprs=templ[row].expr->get_row_exprs();
    strategy_value_exprs[row].insert(
      strategy_value_exprs[row].end(),
      row_exprs.begin(),
      row_exprs.end());

    if(value[row].is_true())
    {
      // !(g=> true)
      cond_exprs[row]=false_exprt();
    }
    else if(value[row].is_false())
    {
      // !(g=> false)
      cond_exprs[row]=
        and_exprt(templ[row].guards.pre_guard, templ[row].guards.post_guard);
    }
    else
    {
      auto &templ_row_expr=dynamic_cast<template_row_exprt &>(*templ[row].expr);
      assert(value[row].c.size()==templ_row_expr.pre_post_values.size());
      assert(value[row].c.size()>=1);

#ifdef DIFFERENCE_ENCODING
      exprt sum=mult_exprt(
        value[row].c[0],
        minus_exprt(
          templ_row_expr.pre_post_values[0].pre,
          templ_row_expr.pre_post_values[0].post));
#else
      exprt sum_pre=mult_exprt(
        value[row].c[0], templ_row_expr.pre_post_values[0].pre);
      exprt sum_post=mult_exprt(
        value[row].c[0], templ_row_expr.pre_post_values[0].post);
#endif
      for(unsigned i=1; i<value[row].c.size(); ++i)
      {
#ifdef DIFFERENCE_ENCODING
        sum=plus_exprt(
          sum,
          mult_exprt(
            value[row].c[i],
            minus_exprt(
              templ_row_expr.pre_post_values[0].pre,
              templ_row_expr.pre_post_values[0].post)));
#else
        sum_pre=plus_exprt(
          sum_pre,
          mult_exprt(value[row].c[i], templ_row_expr.pre_post_values[0].pre));
        sum_post=plus_exprt(
          sum_post,
          mult_exprt(value[row].c[i], templ_row_expr.pre_post_values[0].post));
#endif
      }

#ifdef DIFFERENCE_ENCODING
#ifdef EXTEND_TYPES
      extend_expr_types(sum);
#endif
      exprt decreasing=
        binary_relation_exprt(sum, ID_gt, make_zero(sum.type()));
#else
#ifdef EXTEND_TYPES
      extend_expr_types(sum_pre);
      extend_expr_types(sum_post);
#endif
      exprt decreasing=binary_relation_exprt(sum_pre, ID_gt, sum_post);
#endif
      cond_exprs[row]=not_exprt(
        implies_exprt(
          and_exprt(templ[row].guards.pre_guard, templ[row].guards.post_guard),
          decreasing));
    }
  }
}

exprt linrank_domaint::get_row_symb_constraint(
  linrank_domaint::row_valuet &symb_values, // vector of vars
  const linrank_domaint::rowt &row,
  exprt &refinement_constraint)
{
  // smt_model_values is a vector of values of pre- and post-values
  // two successive elements of the vector correspond to a single symbolic value
  symb_values.c.resize(smt_model_values.size()/2);
  assert(!symb_values.c.empty());
  symb_values.c[0]=symbol_exprt(
    SYMB_COEFF_VAR+std::string("c!")+std::to_string(row)+"$0",
    signedbv_typet(COEFF_C_SIZE));  // coefficients are signed integers

#ifdef DIFFERENCE_ENCODING
  exprt sum=mult_exprt(
    symb_values.c[0],
    minus_exprt(smt_model_values[0], smt_model_values[1]));
#else
  exprt sum_pre=mult_exprt(symb_values.c[0], values[0]);
  exprt sum_post=mult_exprt(symb_values.c[0], values[1]);
#endif
  for(unsigned i=1, vals_i=2; i<symb_values.c.size(); ++i, vals_i+=2)
  {
    symb_values.c[i]=symbol_exprt(
      SYMB_COEFF_VAR+std::string("c!")+std::to_string(row)+"$"+
      std::to_string(i),
      signedbv_typet(COEFF_C_SIZE));  // coefficients are signed integers
#ifdef DIFFERENCE_ENCODING
    sum=plus_exprt(
      sum,
      mult_exprt(
        symb_values.c[i],
        minus_exprt(smt_model_values[vals_i], smt_model_values[vals_i+1])));
#else
    sum_pre=plus_exprt(
      sum_pre,
      mult_exprt(symb_values.c[i], smt_model_values[vals_i]));
    sum_post=plus_exprt(
      sum_post,
      mult_exprt(symb_values.c[i], smt_model_values[vals_i+1]));
#endif
  }

  exprt::operandst constraints;
  exprt::operandst ref_constraints;

#ifdef DIFFERENCE_ENCODING
#ifdef EXTEND_TYPES
  extend_expr_types(sum);
#endif
  exprt decreasing=binary_relation_exprt(sum, ID_gt, make_zero(sum.type()));
#else
#ifdef EXTEND_TYPES
  extend_expr_types(sum_pre);
  extend_expr_types(sum_post);
#endif
  exprt decreasing=binary_relation_exprt(sum_pre, ID_gt, sum_post);
#endif

  constraints.push_back(decreasing);

#if 1
  // refinement
  if(refinement_level==0)
  {
    for(const auto &symb_val : symb_values.c)
    {
      const typet &type=symb_val.type();
      ref_constraints.push_back(
        binary_relation_exprt(symb_val, ID_ge, make_minusone(type)));
      ref_constraints.push_back(
        binary_relation_exprt(symb_val, ID_le, make_one(type)));
    }
  }
  else if(refinement_level==1)
  {
    for(const auto &symb_val : symb_values.c)
    {
      const typet &type=symb_val.type();
      if(type.id()==ID_signedbv || type.id()==ID_unsignedbv)
      {
        ref_constraints.push_back(
          binary_relation_exprt(
            symb_val,
            ID_ge,
            from_integer(mp_integer(-10), type)));
        ref_constraints.push_back(
          binary_relation_exprt(
            symb_val,
            ID_le,
            from_integer(mp_integer(10), type)));
      }
    }
  }
#endif

  refinement_constraint=conjunction(ref_constraints);
  exprt cond=conjunction(constraints);
  adjust_float_expressions(cond, ns);
  return cond;
}

void linrank_domaint::output_value(
  std::ostream &out,
  const domaint::valuet &value,
  const namespacet &ns) const
{
  auto &v=dynamic_cast<const templ_valuet &>(value);
  for(unsigned row=0; row<templ.size(); row++)
  {
    auto &templ_row_expr=dynamic_cast<template_row_exprt &>(*templ[row].expr);
    templ[row].guards.output(out, ns);

    for(unsigned i=0; i<templ_row_expr.pre_post_values.size(); ++i)
    {
      if(i>0)
        out << "+";
      out << from_expr(ns, "", v[row].c[i]) << " * "
          << from_expr(ns, "", templ_row_expr.pre_post_values[i].pre);
    }
    out << std::endl;
  }
}

void linrank_domaint::project_on_vars(
  domaint::valuet &value,
  const var_sett &vars,
  exprt &result)
{
  // don't do any projection
  auto &v=dynamic_cast<const templ_valuet &>(value);
  assert(v.size()==templ.size());
  exprt::operandst c;
  c.reserve(templ.size());
  for(unsigned row=0; row<templ.size(); row++)
  {
    assert(templ[row].guards.kind==guardst::LOOP);

    if(v[row].is_true())
    {
      // (g=> true)
      c.push_back(true_exprt());
    }
    else if(v[row].is_false())
    {
      // (g=> false)
      c.push_back(
        implies_exprt(
          and_exprt(templ[row].guards.pre_guard, templ[row].guards.post_guard),
          false_exprt()));
    }
    else
    {
      auto &templ_row_expr=dynamic_cast<template_row_exprt &>(*templ[row].expr);
      assert(v[row].c.size()==templ_row_expr.pre_post_values.size());
      assert(v[row].c.size()>=1);

#ifdef DIFFERENCE_ENCODING
      exprt sum=mult_exprt(
        v[row].c[0],
        minus_exprt(
          templ_row_expr.pre_post_values[0].pre,
          templ_row_expr.pre_post_values[0].post));
#else
      exprt sum_pre=mult_exprt(
        value[row].c[0], templ_row_expr.pre_post_values[0].pre);
      exprt sum_post=mult_exprt(
        value[row].c[0], templ_row_expr.pre_post_values[0].post);
#endif
      for(unsigned i=1; i<v[row].c.size(); ++i)
      {
#ifdef DIFFERENCE_ENCODING
        sum=plus_exprt(
          sum,
          mult_exprt(
            v[row].c[i],
            minus_exprt(
              templ_row_expr.pre_post_values[0].pre,
              templ_row_expr.pre_post_values[0].post)));
#else
        sum_pre=plus_exprt(
          sum_pre,
          mult_exprt(value[row].c[i], templ_row_expr.pre_post_values[0].pre));
        sum_post=plus_exprt(
          sum_post,
          mult_exprt(value[row].c[i], templ_row_expr.pre_post_values[0].post));
#endif
      }

#ifdef DIFFERENCE_ENCODING
#ifdef EXTEND_TYPES
      extend_expr_types(sum);
#endif
      exprt decreasing=
        binary_relation_exprt(sum, ID_gt, make_zero(sum.type()));
#else
#ifdef EXTEND_TYPES
      extend_expr_types(sum_pre);
      extend_expr_types(sum_post);
#endif
      exprt decreasing=binary_relation_exprt(sum_pre, ID_gt, sum_post);
#endif
      c.push_back(
        implies_exprt(
          and_exprt(templ[row].guards.pre_guard, templ[row].guards.post_guard),
          decreasing));
    }
  }
  result=conjunction(c);
  adjust_float_expressions(result, ns);
}

/// This is called for each loop.
void linrank_domaint::add_template(
  const var_specst &var_specs,
  const namespacet &ns)
{
  bool has_loop=false;
  for(var_specst::const_iterator v=var_specs.begin();
      v!=var_specs.end(); v++)
  {
    if(v->guards.kind==guardst::LOOP)
    {
      has_loop=true;
      break;
    }
  }
  if(!has_loop)
    return;

  templ.reserve(templ.size()+1);
  templ.push_back(template_rowt());
  template_rowt &templ_row=templ.back();
  templ_row.expr=std::unique_ptr<template_row_exprt>(new template_row_exprt());
  auto &templ_row_expr=dynamic_cast<template_row_exprt &>(*templ_row.expr);
  templ_row.guards.kind=guardst::LOOP;

  exprt::operandst preg;
  exprt::operandst postg;

  for(var_specst::const_iterator v=var_specs.begin();
      v!=var_specs.end(); v++)
  {
    if(v->guards.kind!=guardst::LOOP)
      continue;
    preg.push_back(v->guards.pre_guard);
    postg.push_back(v->guards.post_guard);
    exprt vpost=v->var; // copy
    rename(vpost);
    templ_row_expr.pre_post_values.emplace_back(v->var, vpost);
  }

  templ_row.guards.pre_guard=conjunction(preg);
  templ_row.guards.post_guard=conjunction(postg);
}

void linrank_domaint::template_row_exprt::output(
  std::ostream &out,
  const namespacet &ns) const
{
  for(unsigned i=0; i<pre_post_values.size(); ++i)
  {
    if(i>0)
      out << "+";
    out << "c!" << row << "$" << i << " * "
        << from_expr(ns, "", pre_post_values[i].pre);
  }
}

std::vector<exprt> linrank_domaint::template_row_exprt::get_row_exprs()
{
  std::vector<exprt> exprs;
  for(auto &pre_post : pre_post_values)
  {
    exprs.push_back(pre_post.pre);
    exprs.push_back(pre_post.post);
  }
  return exprs;
}
