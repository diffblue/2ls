/*******************************************************************\

Module: Lexicographic linear ranking function domain

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Lexicographic linear ranking function domain

#ifdef DEBUG
#include <iostream>
#endif

#include <util/find_symbols.h>
#include <util/simplify_expr.h>
#include <langapi/languages.h>
#include <goto-symex/adjust_float_expressions.h>

#include <util/cprover_prefix.h>
#include "lexlinrank_domain.h"
#include "util.h"

#define SYMB_COEFF_VAR "symb_coeff#"

#define EXTEND_TYPES
#define DIFFERENCE_ENCODING

#define COEFF_C_SIZE 10
#define MAX_REFINEMENT 2

void lexlinrank_domaint::initialize_value(domaint::valuet &value)
{
  auto &v=dynamic_cast<templ_valuet &>(value);
  v.resize(templ.size());
  for(auto &row : v)
  {
    row.clear();
    row.add_element();
  }
}

void lexlinrank_domaint::initialize()
{
  delete inner_solver;
  inner_solver=incremental_solvert::allocate(ns);
}

bool lexlinrank_domaint::edit_row(const rowt &row, valuet &inv, bool improved)
{
  auto &rank=dynamic_cast<lexlinrank_domaint::templ_valuet &>(inv);
  lexlinrank_domaint::row_valuet symb_values;
  symb_values.resize(rank[row].size());

  exprt constraint;
  exprt refinement_constraint;

  // generate the new constraint
  constraint=get_row_symb_constraint(
    symb_values,
    row,
    refinement_constraint);

  simplify_expr(constraint, ns);
  *inner_solver << constraint;

  exprt rounding_mode=symbol_exprt(
    CPROVER_PREFIX "rounding_mode",
    signedbv_typet(32));

  // set rounding mode
  *inner_solver << equal_exprt(
    rounding_mode,
    from_integer(mp_integer(0), signedbv_typet(32)));

  // refinement
  if(!refinement_constraint.is_true())
  {
    inner_solver->new_context();
    *inner_solver << refinement_constraint;
  }

  // solve
  decision_proceduret::resultt inner_solver_result=(*inner_solver)();
  if(inner_solver_result==decision_proceduret::resultt::D_SATISFIABLE &&
     number_inner_iterations<max_inner_iterations)
  {
    number_inner_iterations++;

    // new_row_values will contain the new values for c and d
    lexlinrank_domaint::row_valuet new_row_values;
    new_row_values.resize(rank[row].size());

    for(std::size_t constraint_no=0;
        constraint_no<symb_values.size(); ++constraint_no)
    {
      std::vector<exprt> c=symb_values[constraint_no].c;

      // get the model for all c
      for(auto &e : c)
      {
        exprt v=inner_solver->solver->get(e);
        new_row_values[constraint_no].c.push_back(v);
      }
    }

    improved=true;

    // update the current template
    rank[row]=new_row_values;

    if(!refinement_constraint.is_true())
      inner_solver->pop_context();
  }
  else
  {
    if(refine())
    {
      improved=true; // refinement possible

      if(!refinement_constraint.is_true())
        inner_solver->pop_context();
    }
    else
    {
      if(number_elements_per_row[row]==max_elements-1)
      {
        // no ranking function for the current template
        rank[row].set_to_true();
        reset_refinements();
      }
      else
      {
        number_elements_per_row[row]++;
        delete inner_solver;
        inner_solver=incremental_solvert::allocate(ns);
        reset_refinements();

        rank[row].add_element();
        number_inner_iterations=0;
        improved=true;
      }
    }
  }
  return improved;
}

exprt lexlinrank_domaint::to_pre_constraints(const valuet &_value)
{
  exprt rounding_mode=symbol_exprt(
    CPROVER_PREFIX "rounding_mode",
    signedbv_typet(32));

  return equal_exprt(
    rounding_mode,
    from_integer(mp_integer(0), signedbv_typet(32)));
}

void lexlinrank_domaint::init_value_solver_iteration(domaint::valuet &_rank)
{
  auto &rank=dynamic_cast<templ_valuet &>(_rank);
  number_elements_per_row.resize(rank.size());
}

bool lexlinrank_domaint::handle_unsat(valuet &value, bool improved)
{
  reset_refinements();
  return improved;
}

bool lexlinrank_domaint::refine()
{
  if(refinement_level>=MAX_REFINEMENT)
    return false;
  refinement_level++;
  return true;
}

void lexlinrank_domaint::reset_refinements()
{
  refinement_level=0;
}

void lexlinrank_domaint::make_not_post_constraints(
  const valuet &_value,
  exprt::operandst &cond_exprs)
{
  auto &value=dynamic_cast<const templ_valuet &>(_value);
  cond_exprs.resize(value.size());
  strategy_value_exprs.resize(value.size());

  for(std::size_t row=0; row<templ.size(); row++)
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
      exprt::operandst elmts;
      elmts.reserve(value[row].size());
      for(std::size_t elm=0; elm<value[row].size(); ++elm)
      {
        auto &templ_row_expr=
          dynamic_cast<template_row_exprt &>(*templ[row].expr);
        assert(value[row][elm].c.size()==templ_row_expr.pre_post_values.size());
        assert(value[row][elm].c.size()>=1);

        exprt::operandst c;
        c.reserve(1+value[row].size()-(elm+1));

#ifdef DIFFERENCE_ENCODING
        exprt sum=
          mult_exprt(
            value[row][elm].c[0],
            minus_exprt(
              templ_row_expr.pre_post_values[0].pre,
              templ_row_expr.pre_post_values[0].post));
#else
        exprt sum_pre=
          mult_exprt(
            value[row][elm].c[0], templ_row_expr.pre_post_values[0].pre);
        exprt sum_post=
          mult_exprt(
            value[row][elm].c[0], templ_row_expr.pre_post_values[0].post);
#endif
        for(std::size_t i=1; i<value[row][elm].c.size(); ++i)
        {
#ifdef DIFFERENCE_ENCODING
          sum=plus_exprt(
            sum,
            mult_exprt(
              value[row][elm].c[i],
              minus_exprt(
                templ_row_expr.pre_post_values[i].pre,
                templ_row_expr.pre_post_values[i].post)));
#else
          sum_pre=plus_exprt(
            sum_pre,
            mult_exprt(
              value[row][elm].c[i],
              templ_row_expr.pre_post_values[i].pre));
          sum_post=plus_exprt(
            sum_post,
            mult_exprt(
              value[row][elm].c[i],
              templ_row_expr.pre_post_values[i].post));
#endif
        }
        // extend types
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

        c.push_back(decreasing);

        for(std::size_t elm2=elm+1; elm2<value[row].size(); ++elm2)
        {
#ifdef DIFFERENCE_ENCODING
          exprt sum2=mult_exprt(
            value[row][elm2].c[0],
            minus_exprt(
              templ_row_expr.pre_post_values[0].pre,
              templ_row_expr.pre_post_values[0].post));
#else
          exprt sum_pre2=
            mult_exprt(
              value[row][elm2].c[0], templ_row_expr.pre_post_values[0].pre);
          exprt sum_post2=
            mult_exprt(
              value[row][elm2].c[0], templ_row_expr.pre_post_values[0].post);
#endif
          for(std::size_t i=1; i<value[row][elm2].c.size(); ++i)
          {
#ifdef DIFFERENCE_ENCODING
            sum2=plus_exprt(
              sum2,
              mult_exprt(
                value[row][elm2].c[i],
                minus_exprt(
                  templ_row_expr.pre_post_values[i].pre,
                  templ_row_expr.pre_post_values[i].post)));
#else
            sum_pre2=plus_exprt(
              sum_pre2,
              mult_exprt(
                value[row][elm2].c[i],
                templ_row_expr.pre_post_values[i].pre));
            sum_post2=plus_exprt(
              sum_post2,
              mult_exprt(
                value[row][elm2].c[i],
                templ_row_expr.pre_post_values[i].pre));
#endif
          }

#ifdef DIFFERENCE_ENCODING
#ifdef EXTEND_TYPES
          extend_expr_types(sum2);
#endif
          exprt non_inc=
            binary_relation_exprt(sum2, ID_ge, make_zero(sum2.type()));
#else
#ifdef EXTEND_TYPES
          extend_expr_types(sum_pre2);
          extend_expr_types(sum_post2);
#endif
          exprt non_inc=binary_relation_exprt(sum_pre2, ID_ge, sum_post2);
#endif

          c.push_back(non_inc);
        }

        elmts.push_back(conjunction(c));
      }

      cond_exprs[row]=not_exprt(
        implies_exprt(
          and_exprt(templ[row].guards.pre_guard, templ[row].guards.post_guard),
          disjunction(elmts)));
    }
  }
}

exprt lexlinrank_domaint::get_row_symb_constraint(
  row_valuet &symb_values, // contains vars c and d
  const rowt &row,
  exprt &refinement_constraint)
{
  // NOTE: I assume symb_values.size was set to the number of
  // desired elements in the lexicographic before calling this function

  exprt::operandst d;
  d.reserve(symb_values.size());

  // we iterate in reverse as we init symbols the inner iteration uses
  for(int elm=symb_values.size()-1; elm>=0; --elm)
  {
    // smt_model_values is a vector of values of pre- and post-values
    // two successive elements of the vector correspond to a single symbolic
    // value
    symb_values[elm].c.resize(smt_model_values.size()/2);
    assert(!symb_values[elm].c.empty());

    exprt::operandst c;
    c.reserve(1+symb_values.size()-(elm+1));

    symb_values[elm].c[0]=symbol_exprt(
      SYMB_COEFF_VAR+std::string("c!")+
      std::to_string(row)+"$"+std::to_string(elm)+"$0",
      signedbv_typet(COEFF_C_SIZE));  // coefficients are signed integers

#ifdef DIFFERENCE_ENCODING
    exprt sum=mult_exprt(
      symb_values[elm].c[0],
      minus_exprt(smt_model_values[0], smt_model_values[1]));
#else
    exprt sum_pre=mult_exprt(symb_values[elm].c[0], smt_model_values[0]);
    exprt sum_post=mult_exprt(symb_values[elm].c[0], smt_model_values[0]);
#endif

    for(std::size_t i=1, vals_i=2; i<symb_values[elm].c.size(); ++i, vals_i+=2)
    {
      symb_values[elm].c[i]=symbol_exprt(
        SYMB_COEFF_VAR+std::string("c!")+
        std::to_string(row)+"$"+std::to_string(elm)+"$"+std::to_string(i),
        signedbv_typet(COEFF_C_SIZE));
#ifdef DIFFERENCE_ENCODING
      sum=plus_exprt(
        sum,
        mult_exprt(
          symb_values[elm].c[i],
          minus_exprt(smt_model_values[vals_i], smt_model_values[vals_i+1])));
#else
      sum_pre=plus_exprt(
        sum_pre,
        mult_exprt(symb_values[elm].c[i], smt_model_values[vals_i]));
      sum_post=plus_exprt(
        sum_post,
        mult_exprt(symb_values[elm].c[i], smt_model_values[vals_i+1]));
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

    c.push_back(decreasing);

    for(std::size_t elm2=elm+1; elm2<symb_values.size(); ++elm2)
    {
#ifdef DIFFERENCE_ENCODING
      exprt sum2=mult_exprt(
        symb_values[elm2].c[0],
        minus_exprt(smt_model_values[0], smt_model_values[1]));
#else
      exprt sum_pre2=mult_exprt(symb_values[elm2].c[0], smt_model_values[0]);
      exprt sum_post2=mult_exprt(symb_values[elm2].c[0], smt_model_values[1]);
#endif

      for(std::size_t i=1, vals_i=2;
          i<symb_values[elm2].c.size(); ++i, vals_i+=2)
      {
#ifdef DIFFERENCE_ENCODING
        sum2=plus_exprt(
          sum2,
          mult_exprt(
            symb_values[elm2].c[i],
            minus_exprt(smt_model_values[vals_i], smt_model_values[vals_i+1])));
#else
        sum_pre2=plus_exprt(
          sum_pre2,
          mult_exprt(symb_values[elm2].c[i], smt_model_values[vals_i]));
        sum_post2=plus_exprt(
          sum_post2,
          mult_exprt(symb_values[elm2].c[i], smt_model_values[vals_i+1]));
#endif
      }

#ifdef DIFFERENCE_ENCODING
#ifdef EXTEND_TYPES
      extend_expr_types(sum2);
#endif
      exprt non_inc=
        binary_relation_exprt(sum2, ID_ge, make_zero(sum.type()));
#else
#ifdef EXTEND_TYPES
      extend_expr_types(sum_pre2);
      extend_expr_types(sum_post2);
#endif
      exprt non_inc=binary_relation_exprt(sum_pre2, ID_ge, sum_post2);
#endif
      c.push_back(non_inc);
    }

    d.push_back(conjunction(c));
  }

  exprt::operandst ref_constraints;
#if 1
  // refinement
  if(refinement_level==0)
  {
    for(auto &elm : symb_values)
    {
      for(auto &symb_val : elm.c)
      {
        ref_constraints.push_back(
          binary_relation_exprt(
            symb_val,
            ID_ge,
            make_minusone(symb_val.type())));
        ref_constraints.push_back(
          binary_relation_exprt(
            symb_val,
            ID_le,
            make_one(symb_val.type())));
      }
    }
  }
  else if(refinement_level==1)
  {
    for(auto &elm : symb_values)
    {
      for(auto &symb_val : elm.c)
      {
        ref_constraints.push_back(
          binary_relation_exprt(
            symb_val,
            ID_ge,
            from_integer(mp_integer(-10), symb_val.type())));
        ref_constraints.push_back(
          binary_relation_exprt(
            symb_val,
            ID_le,
            from_integer(mp_integer(10), symb_val.type())));
      }
    }
  }
#endif

  refinement_constraint=conjunction(ref_constraints);

  exprt dd=disjunction(d);
  adjust_float_expressions(dd, ns);
  return dd;
}

void lexlinrank_domaint::output_value(
  std::ostream &out,
  const domaint::valuet &value,
  const namespacet &ns) const
{
  auto &v=dynamic_cast<const templ_valuet &>(value);
  for(std::size_t row=0; row<templ.size(); row++)
  {
    auto &templ_row_expr=dynamic_cast<template_row_exprt &>(*templ[row].expr);
    templ[row].guards.output(out, ns);

    for(std::size_t elm=0; elm<v[row].size(); ++elm)
    {
      out << "       ";
      for(std::size_t i=0; i<templ_row_expr.pre_post_values.size(); ++i)
      {
        if(i>0)
          out << "+";
        out << from_expr(ns, "", v[row][elm].c[i]) << " * "
            << from_expr(ns, "", templ_row_expr.pre_post_values[i].pre);
      }
      out << std::endl;
    }
  }
}

void lexlinrank_domaint::project_on_vars(
  domaint::valuet &value,
  const var_sett &vars,
  exprt &result)
{
  // don't do any projection
  auto &v=dynamic_cast<const templ_valuet &>(value);
  assert(v.size()==templ.size());
  exprt::operandst c; // c is the conjunction of all rows
  c.reserve(templ.size());
  for(std::size_t row=0; row<templ.size(); ++row)
  {
    assert(templ[row].guards.kind==guardst::LOOP);

    if(v[row].is_false())
    {
      // (g=> false)
      c.push_back(
        implies_exprt(
          and_exprt(templ[row].guards.pre_guard, templ[row].guards.post_guard),
          false_exprt()));
    }
    else if(v[row].is_true())
    {
      // (g=> true)
      c.push_back(
        implies_exprt(
          and_exprt(templ[row].guards.pre_guard, templ[row].guards.post_guard),
          true_exprt()));
    }
    else
    {
      exprt::operandst d; // d is the disjunction of lexicographic elements
      d.reserve(v[row].size());
      auto &templ_row_expr=dynamic_cast<template_row_exprt &>(*templ[row].expr);
      for(std::size_t elm=0; elm<v[row].size(); ++elm)
      {
        assert(v[row][elm].c.size()==templ_row_expr.pre_post_values.size());
        assert(v[row][elm].c.size()>=1);

        // con is the constraints for a single element of the lexicography
        exprt::operandst con;
        con.reserve(1+v[row].size()-(elm+1));

        exprt sum=mult_exprt(
          v[row][elm].c[0],
          minus_exprt(
            templ_row_expr.pre_post_values[0].pre,
            templ_row_expr.pre_post_values[0].post));

        for(std::size_t i=1; i<v[row][elm].c.size(); ++i)
        {
          sum=plus_exprt(
            sum,
            mult_exprt(
              v[row][elm].c[i],
              minus_exprt(
                templ_row_expr.pre_post_values[i].pre,
                templ_row_expr.pre_post_values[i].post)));
        }
        // extend types
#ifdef EXTEND_TYPES
        extend_expr_types(sum);
#endif
        exprt decreasing=
          binary_relation_exprt(sum, ID_gt, make_zero(sum.type()));
        con.push_back(decreasing);

        for(std::size_t elm2=elm+1; elm2<v[row].size(); ++elm2)
        {
          exprt sum2=mult_exprt(
            v[row][elm2].c[0],
            minus_exprt(
              templ_row_expr.pre_post_values[0].pre,
              templ_row_expr.pre_post_values[0].post));

          for(std::size_t i=1; i<v[row][elm2].c.size(); ++i)
          {
            sum2=plus_exprt(
              sum2,
              mult_exprt(
                v[row][elm2].c[i],
                minus_exprt(
                  templ_row_expr.pre_post_values[i].pre,
                  templ_row_expr.pre_post_values[i].post)));
          }
          // extend types
#ifdef EXTEND_TYPES
          extend_expr_types(sum2);
#endif
          exprt non_inc=
            binary_relation_exprt(sum2, ID_ge, make_zero(sum.type()));
          con.push_back(non_inc);
        }

        d.push_back(conjunction(con));
      }

      c.push_back(
        implies_exprt(
          and_exprt(templ[row].guards.pre_guard, templ[row].guards.post_guard),
          disjunction(d)));
    }
  }
  result=conjunction(c);
  adjust_float_expressions(result, ns);
}

/// This is called for each loop.
void lexlinrank_domaint::add_template(
  const var_specst &var_specs,
  const namespacet &ns)
{
  bool has_loop=false;
  for(const auto &v : var_specs)
  {
    if(v.guards.kind==guardst::LOOP)
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

  for(const auto &v : var_specs)
  {
    if(v.guards.kind!=guardst::LOOP)
      continue;
    preg.push_back(v.guards.pre_guard);
    postg.push_back(v.guards.post_guard);
    exprt vpost=v.var; // copy
    rename(vpost);
    templ_row_expr.pre_post_values.emplace_back(v.var, vpost);
  }

  templ_row.guards.pre_guard=conjunction(preg);
  templ_row.guards.post_guard=conjunction(postg);
}

std::vector<exprt> lexlinrank_domaint::template_row_exprt::get_row_exprs()
{
  std::vector<exprt> exprs;
  for(auto &pre_post : pre_post_values)
  {
    exprs.push_back(pre_post.pre);
    exprs.push_back(pre_post.post);
  }
  return exprs;
}

void lexlinrank_domaint::template_row_exprt::output(
  std::ostream &out,
  const namespacet &ns) const
{
  for(std::size_t i=0; i<pre_post_values.size(); ++i)
  {
    if(i>0)
      out << "+";
    out << "c!" << row << "$" << i << " * "
        << from_expr(ns, "", pre_post_values[i].pre);
  }
}
