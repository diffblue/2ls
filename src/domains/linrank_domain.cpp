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
#include <util/i2string.h>
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

void linrank_domaint::initialize(valuet &value)
{
  templ_valuet &v=static_cast<templ_valuet&>(value);
  v.resize(templ.size());
  for(unsigned row=0; row<templ.size(); row++)
  {
    v[row].c.resize(1);
    v[row].c[0]=false_exprt();
  }
}

std::vector<exprt> linrank_domaint::get_required_smt_values(size_t row)
{
  std::vector<exprt> r;
  for(auto &row_expr : strategy_value_exprs[row])
  {
    r.push_back(row_expr.first);
    r.push_back(row_expr.second);
  }
  return r;
}

void linrank_domaint::set_smt_values(std::vector<exprt> got_values, size_t row)
{
  values.clear();
  for(size_t i=0; i<got_values.size(); i+=2)
    values.push_back(std::make_pair(got_values[i], got_values[i+1]));
}

bool linrank_domaint::edit_row(const rowt &row, valuet &inv, bool improved)
{
  linrank_domaint::templ_valuet &rank=
    static_cast<linrank_domaint::templ_valuet &>(inv);
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
  if((*inner_solver)()==decision_proceduret::D_SATISFIABLE &&
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
    set_row_value(row, new_row_values, rank);

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
      set_row_value_to_true(row, rank);
      reset_refinements();
    }
  }

  if(!refinement_constraint.is_true())
    inner_solver->pop_context();

  return improved;
}

exprt linrank_domaint::to_pre_constraints(valuet &_value)
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
  valuet &_value,
  exprt::operandst &cond_exprs)
{
  linrank_domaint::templ_valuet &value=
    static_cast<linrank_domaint::templ_valuet &>(_value);
  assert(value.size()==templ.size());
  cond_exprs.resize(value.size());
  strategy_value_exprs.resize(value.size());

  for(unsigned row=0; row<templ.size(); row++)
  {
    strategy_value_exprs[row].insert(
      strategy_value_exprs[row].end(),
      templ[row].expr.begin(),
      templ[row].expr.end());

    if(is_row_value_true(value[row]))
    {
      // !(g=> true)
      cond_exprs[row]=false_exprt();
    }
    else if(is_row_value_false(value[row]))
    {
      // !(g=> false)
      cond_exprs[row]=
        and_exprt(templ[row].pre_guard, templ[row].post_guard);
    }
    else
    {
      assert(value[row].c.size()==templ[row].expr.size());
      assert(value[row].c.size()>=1);

#ifdef DIFFERENCE_ENCODING
      exprt sum=mult_exprt(
        value[row].c[0],
        minus_exprt(templ[row].expr[0].first, templ[row].expr[0].second));
#else
      exprt sum_pre=mult_exprt(value[row].c[0], templ[row].expr[0].first);
      exprt sum_post=mult_exprt(value[row].c[0], templ[row].expr[0].second);
#endif
      for(unsigned i=1; i<value[row].c.size(); ++i)
      {
#ifdef DIFFERENCE_ENCODING
        sum=plus_exprt(
          sum,
          mult_exprt(
            value[row].c[i],
            minus_exprt(templ[row].expr[i].first, templ[row].expr[i].second)));
#else
        sum_pre=plus_exprt(
          sum_pre,
          mult_exprt(value[row].c[i], templ[row].expr[i].first));
        sum_post=plus_exprt(
          sum_post,
          mult_exprt(value[row].c[i], templ[row].expr[i].second));
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
          and_exprt(templ[row].pre_guard, templ[row].post_guard),
          decreasing));
    }
  }
}

exprt linrank_domaint::get_row_symb_constraint(
  linrank_domaint::row_valuet &symb_values, // contains vars c
  const linrank_domaint::rowt &row,
  exprt &refinement_constraint)
{
  symb_values.c.resize(values.size());
  assert(values.size()>=1);
  symb_values.c[0]=symbol_exprt(
    SYMB_COEFF_VAR+std::string("c!")+i2string(row)+"$0",
    signedbv_typet(COEFF_C_SIZE));  // coefficients are signed integers

#ifdef DIFFERENCE_ENCODING
  exprt sum=mult_exprt(
    symb_values.c[0],
    minus_exprt(values[0].first, values[0].second));
#else
  exprt sum_pre=mult_exprt(symb_values.c[0], values[0].first);
  exprt sum_post=mult_exprt(symb_values.c[0], values[0].second);
#endif
  for(unsigned i=1; i<symb_values.c.size(); ++i)
  {
    symb_values.c[i]=symbol_exprt(
      SYMB_COEFF_VAR+std::string("c!")+i2string(row)+"$"+i2string(i),
      signedbv_typet(COEFF_C_SIZE));  // coefficients are signed integers
#ifdef DIFFERENCE_ENCODING
    sum=plus_exprt(
      sum,
      mult_exprt(
        symb_values.c[i],
        minus_exprt(values[i].first, values[i].second)));
#else
    sum_pre=plus_exprt(
      sum_pre,
      mult_exprt(symb_values.c[i], values[i].first));
    sum_post=plus_exprt(
      sum_post,
      mult_exprt(symb_values.c[i], values[i].second));
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
    for(unsigned i=0; i<values.size(); ++i)
    {
      typet type=symb_values.c[i].type();
      ref_constraints.push_back(
        binary_relation_exprt(symb_values.c[i], ID_ge, make_minusone(type)));
      ref_constraints.push_back(
        binary_relation_exprt(symb_values.c[i], ID_le, make_one(type)));
    }
  }
  else if(refinement_level==1)
  {
    for(unsigned i=0; i<values.size(); ++i)
    {
      typet type=symb_values.c[i].type();
      if(type.id()==ID_signedbv || type.id()==ID_unsignedbv)
      {
        ref_constraints.push_back(
          binary_relation_exprt(
            symb_values.c[i],
            ID_ge,
            from_integer(mp_integer(-10), type)));
        ref_constraints.push_back(
          binary_relation_exprt(
            symb_values.c[i],
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

linrank_domaint::row_valuet linrank_domaint::get_row_value(
  const rowt &row,
  const templ_valuet &value)
{
  assert(row<value.size());
  assert(value.size()==templ.size());
  return value[row];
}

void linrank_domaint::set_row_value(
  const rowt &row,
  const row_valuet &row_value,
  templ_valuet &value)
{
  assert(row<value.size());
  assert(value.size()==templ.size());
  value[row]=row_value;
}

void linrank_domaint::set_row_value_to_true(
  const rowt &row,
  templ_valuet &value)
{
  assert(row<value.size());
  assert(value.size()==templ.size());
  value[row].c.resize(1);
  value[row].c[0]=true_exprt();
}

void linrank_domaint::output_value(
  std::ostream &out,
  const valuet &value,
  const namespacet &ns) const
{
  const templ_valuet &v=static_cast<const templ_valuet &>(value);
  for(unsigned row=0; row<templ.size(); row++)
  {
    const template_rowt &templ_row=templ[row];
    switch(templ_row.kind)
    {
    case LOOP:
      out << "(RANK) [ " << from_expr(ns, "", templ_row.pre_guard) << " | ";
      out << from_expr(ns, "", templ_row.post_guard)
          << " ]===> " << std::endl << "       ";
      break;
    default: assert(false);
    }

    for(unsigned i=0; i<templ_row.expr.size(); ++i)
    {
      if(i>0)
        out << "+";
      out << from_expr(ns, "", v[row].c[i]) << " * "
          << from_expr(ns, "", templ_row.expr[i].first);
    }
    out << std::endl;
  }
}

void linrank_domaint::output_domain(
  std::ostream &out,
  const namespacet &ns) const
{
  for(unsigned row=0; row<templ.size(); row++)
  {
    const template_rowt &templ_row=templ[row];
    switch(templ_row.kind)
    {
    case LOOP:
      out << "(RANK) (" << from_expr(ns, "", templ_row.pre_guard)
          << ") && (" << from_expr(ns, "", templ_row.post_guard) << ")===> "
          << std::endl << "      ";
      break;
    default: assert(false);
    }

    for(unsigned i=0; i<templ_row.expr.size(); ++i)
    {
      if(i>0)
        out << "+";
      out << "c!" << row << "$" << i << " * "
          << from_expr(ns, "", templ_row.expr[i].first);
    }
    out << std::endl;
  }
}

void linrank_domaint::project_on_vars(
  valuet &value,
  const var_sett &vars,
  exprt &result)
{
  // don't do any projection
  const templ_valuet &v=static_cast<const templ_valuet &>(value);
  assert(v.size()==templ.size());
  exprt::operandst c;
  c.reserve(templ.size());
  for(unsigned row=0; row<templ.size(); row++)
  {
    assert(templ[row].kind==LOOP);

    if(is_row_value_true(v[row]))
    {
      // (g=> true)
      c.push_back(true_exprt());
    }
    else if(is_row_value_false(v[row]))
    {
      // (g=> false)
      c.push_back(
        implies_exprt(
          and_exprt(templ[row].pre_guard, templ[row].post_guard),
          false_exprt()));
    }
    else
    {
      assert(v[row].c.size()==templ[row].expr.size());
      assert(v[row].c.size()>=1);

#ifdef DIFFERENCE_ENCODING
      exprt sum=mult_exprt(
        v[row].c[0],
        minus_exprt(templ[row].expr[0].first, templ[row].expr[0].second));
#else
      exprt sum_pre=mult_exprt(v[row].c[0], templ[row].expr[0].first);
      exprt sum_post=mult_exprt(v[row].c[0], templ[row].expr[0].second);
#endif
      for(unsigned i=1; i<v[row].c.size(); ++i)
      {
#ifdef DIFFERENCE_ENCODING
        sum=plus_exprt(
          sum,
          mult_exprt(
            v[row].c[i],
            minus_exprt(templ[row].expr[i].first, templ[row].expr[i].second)));
#else
        sum_pre=plus_exprt(
          sum_pre,
          mult_exprt(v[row].c[i], templ[row].expr[i].first));
        sum_post=plus_exprt(
          sum_post,
          mult_exprt(v[row].c[i], templ[row].expr[i].second));
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
          and_exprt(templ[row].pre_guard, templ[row].post_guard),
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
    if(v->kind==LOOP)
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
  templ_row.kind=LOOP;

  exprt::operandst preg;
  exprt::operandst postg;

  for(var_specst::const_iterator v=var_specs.begin();
      v!=var_specs.end(); v++)
  {
    if(v->kind!=LOOP)
      continue;
    preg.push_back(v->pre_guard);
    postg.push_back(v->post_guard);
    exprt vpost=v->var; // copy
    rename(vpost);
    templ_row.expr.push_back(std::pair<exprt, exprt>(v->var, vpost));
  }

  templ_row.pre_guard=conjunction(preg);
  templ_row.post_guard=conjunction(postg);
}

bool linrank_domaint::is_row_value_false(const row_valuet & row_value) const
{
  assert(row_value.c.size()>=1);
  return row_value.c[0].get(ID_value)==ID_false;
}

bool linrank_domaint::is_row_value_true(const row_valuet & row_value) const
{
  assert(row_value.c.size()>=1);
  return row_value.c[0].get(ID_value)==ID_true;
}
