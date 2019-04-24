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
#include <util/i2string.h>
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

void lexlinrank_domaint::initialize(valuet &value)
{
  templ_valuet &v=static_cast<templ_valuet &>(value);
  v.resize(templ.size());
  for(auto &row : v)
  {
    row.resize(1);
    row[0].c.resize(1);
    row[0].c[0]=false_exprt();
  }
}

const exprt lexlinrank_domaint::initialize_solver(
  const local_SSAt &SSA,
  const exprt &precondition,
  template_generator_baset &template_generator)
{
  delete inner_solver;
  inner_solver=incremental_solvert::allocate(ns);

  return true_exprt();
}

bool lexlinrank_domaint::edit_row(const rowt &row, valuet &inv, bool improved)
{
  lexlinrank_domaint::templ_valuet &rank=
    static_cast<lexlinrank_domaint::templ_valuet &>(inv);
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
  bool inner_solver_result=(*inner_solver)();
  if(inner_solver_result==decision_proceduret::D_SATISFIABLE &&
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
    set_row_value(row, new_row_values, rank);

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
        set_row_value_to_true(row, rank);
        reset_refinements();
      }
      else
      {
        number_elements_per_row[row]++;
        delete inner_solver;
        inner_solver=incremental_solvert::allocate(ns);
        reset_refinements();

        add_element(row, rank);
        number_inner_iterations=0;
        improved=true;
      }
    }
  }
  return improved;
}

exprt lexlinrank_domaint::to_pre_constraints(valuet &_value)
{
  exprt rounding_mode=symbol_exprt(
    CPROVER_PREFIX "rounding_mode",
    signedbv_typet(32));

  return equal_exprt(
    rounding_mode,
    from_integer(mp_integer(0), signedbv_typet(32)));
}

void lexlinrank_domaint::solver_iter_init(domaint::valuet &_rank)
{
  lexlinrank_domaint::templ_valuet &rank=
    static_cast<lexlinrank_domaint::templ_valuet &>(_rank);
  number_elements_per_row.resize(rank.size());
}

std::vector<exprt> lexlinrank_domaint::get_required_smt_values(size_t row)
{
  std::vector<exprt> r;
  for(auto &row_expr : strategy_value_exprs[row])
  {
    r.push_back(row_expr.first);
    r.push_back(row_expr.second);
  }
  return r;
}

void lexlinrank_domaint::set_smt_values(
  std::vector<exprt> got_values,
  size_t row)
{
  values.clear();
  for(size_t i=0; i<got_values.size(); i+=2)
    values.push_back(std::make_pair(got_values[i], got_values[i+1]));
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
  valuet &_value,
  exprt::operandst &cond_exprs)
{
  lexlinrank_domaint::templ_valuet &value=
    static_cast<lexlinrank_domaint::templ_valuet &>(_value);
  cond_exprs.resize(value.size());
  strategy_value_exprs.resize(value.size());

for(std::size_t row=0; row<templ.size(); row++)
  {
    strategy_value_exprs[row]=templ[row].expr;

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
      exprt::operandst elmts;
      elmts.reserve(value[row].size());
      for(std::size_t elm=0; elm<value[row].size(); ++elm)
      {
        assert(value[row][elm].c.size()==templ[row].expr.size());
        assert(value[row][elm].c.size()>=1);

        exprt::operandst c;
        c.reserve(1+value[row].size()-(elm+1));

#ifdef DIFFERENCE_ENCODING
        exprt sum=
          mult_exprt(
            value[row][elm].c[0],
            minus_exprt(templ[row].expr[0].first, templ[row].expr[0].second));
#else
        exprt sum_pre=
          mult_exprt(value[row][elm].c[0], templ[row].expr[0].first);
        exprt sum_post=
          mult_exprt(value[row][elm].c[0], templ[row].expr[0].second);
#endif
        for(std::size_t i=1; i<value[row][elm].c.size(); ++i)
        {
#ifdef DIFFERENCE_ENCODING
          sum=plus_exprt(
            sum,
            mult_exprt(
              value[row][elm].c[i],
              minus_exprt(
                templ[row].expr[i].first,
                templ[row].expr[i].second)));
#else
          sum_pre=plus_exprt(
            sum_pre,
            mult_exprt(
              value[row][elm].c[i],
              templ[row].expr[i].first));
          sum_post=plus_exprt(
            sum_post,
            mult_exprt(value[row][elm].c[i], templ[row].expr[i].second));
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
            minus_exprt(templ[row].expr[0].first, templ[row].expr[0].second));
#else
          exprt sum_pre2=
            mult_exprt(value[row][elm2].c[0], templ[row].expr[0].first);
          exprt sum_post2=
            mult_exprt(value[row][elm2].c[0], templ[row].expr[0].first);
#endif
          for(std::size_t i=1; i<value[row][elm2].c.size(); ++i)
          {
#ifdef DIFFERENCE_ENCODING
            sum2=plus_exprt(
              sum2,
              mult_exprt(
                value[row][elm2].c[i],
                minus_exprt(
                  templ[row].expr[i].first,
                  templ[row].expr[i].second)));
#else
            sum_pre2=plus_exprt(
              sum_pre2,
              mult_exprt(value[row][elm2].c[i], templ[row].expr[i].first));
            sum_post2=plus_exprt(
              sum_post2,
              mult_exprt(value[row][elm2].c[i], templ[row].expr[i].second));
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
          and_exprt(templ[row].pre_guard, templ[row].post_guard),
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
    symb_values[elm].c.resize(values.size());
    assert(values.size()>=1);

    exprt::operandst c;
    c.reserve(1+symb_values.size()-(elm+1));

    symb_values[elm].c[0]=symbol_exprt(
      SYMB_COEFF_VAR+std::string("c!")+
      i2string(row)+"$"+i2string(elm)+"$0",
      signedbv_typet(COEFF_C_SIZE));  // coefficients are signed integers

#ifdef DIFFERENCE_ENCODING
    exprt sum=mult_exprt(
      symb_values[elm].c[0],
      minus_exprt(values[0].first, values[0].second));
#else
    exprt sum_pre=mult_exprt(symb_values[elm].c[0], values[0].first);
    exprt sum_post=mult_exprt(symb_values[elm].c[0], values[0].second);
#endif

    for(std::size_t i=1; i<values.size(); ++i)
    {
      symb_values[elm].c[i]=symbol_exprt(
        SYMB_COEFF_VAR+std::string("c!")+
          i2string(row)+"$"+i2string(elm)+"$"+i2string(i),
        signedbv_typet(COEFF_C_SIZE));
#ifdef DIFFERENCE_ENCODING
      sum=plus_exprt(
        sum,
        mult_exprt(
          symb_values[elm].c[i],
          minus_exprt(values[i].first, values[i].second)));
#else
      sum_pre=plus_exprt(
        sum_pre,
        mult_exprt(symb_values[elm].c[i], values[i].first));
      sum_post=plus_exprt(
        sum_post,
        mult_exprt(symb_values[elm].c[i], values[i].second));
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
        minus_exprt(values[0].first, values[0].second));
#else
      exprt sum_pre2=mult_exprt(symb_values[elm2].c[0], values[0].first);
      exprt sum_post2=mult_exprt(symb_values[elm2].c[0], values[0].second);
#endif

      for(std::size_t i=1; i<values.size(); ++i)
      {
#ifdef DIFFERENCE_ENCODING
        sum2=plus_exprt(
          sum2,
          mult_exprt(
            symb_values[elm2].c[i],
            minus_exprt(values[i].first, values[i].second)));
#else
        sum_pre2=plus_exprt(
          sum_pre2,
          mult_exprt(symb_values[elm2].c[i], values[i].first));
        sum_post2=plus_exprt(
          sum_post2,
          mult_exprt(symb_values[elm2].c[i], values[i].second));
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
    for(std::size_t elm=0; elm<symb_values.size(); ++elm)
    {
      for(std::size_t i=0; i<values.size(); ++i)
      {
        ref_constraints.push_back(
          binary_relation_exprt(
            symb_values[elm].c[i],
            ID_ge,
            make_minusone(symb_values[elm].c[i].type())));
        ref_constraints.push_back(
          binary_relation_exprt(
            symb_values[elm].c[i],
            ID_le,
            make_one(symb_values[elm].c[i].type())));
      }
    }
  }
  else if(refinement_level==1)
  {
    for(std::size_t elm=0; elm<symb_values.size(); ++elm)
    {
      for(std::size_t i=0; i<values.size(); ++i)
      {
        ref_constraints.push_back(
          binary_relation_exprt(
            symb_values[elm].c[i],
            ID_ge,
            from_integer(mp_integer(-10), symb_values[elm].c[i].type())));
        ref_constraints.push_back(
          binary_relation_exprt(
            symb_values[elm].c[i],
            ID_le,
            from_integer(mp_integer(10), symb_values[elm].c[i].type())));
      }
    }
  }
#endif

  refinement_constraint=conjunction(ref_constraints);

  exprt dd=disjunction(d);
  adjust_float_expressions(dd, ns);
  return dd;
}

lexlinrank_domaint::row_valuet lexlinrank_domaint::get_row_value(
  const rowt &row,
  const templ_valuet &value)
{
  assert(row<value.size());
  assert(value.size()==templ.size());
  return value[row];
}

void lexlinrank_domaint::set_row_value(
  const rowt &row,
  const row_valuet &row_value,
  templ_valuet &value)
{
  assert(row<value.size());
  assert(value.size()==templ.size());
  value[row]=row_value;
}

void lexlinrank_domaint::set_row_value_to_true(
  const rowt &row,
  templ_valuet &value)
{
  assert(row<value.size());
  assert(value.size()==templ.size());
  value[row].resize(1);
  value[row][0].c.resize(1);
  value[row][0].c[0]=true_exprt();
}

void lexlinrank_domaint::output_value(
  std::ostream &out,
  const valuet &value,
  const namespacet &ns) const
{
  const templ_valuet &v=static_cast<const templ_valuet &>(value);
  for(std::size_t row=0; row<templ.size(); row++)
  {
    const template_rowt &templ_row=templ[row];
    switch(templ_row.kind)
    {
    case LOOP:
      out << "(RANK) [ " << from_expr(ns, "", templ_row.pre_guard) << " | ";
      out << from_expr(ns, "", templ_row.post_guard) << " ]===> " << std::endl;
      break;
    default: assert(false);
    }

    for(std::size_t elm=0; elm<v[row].size(); ++elm)
    {
      out << "       ";
      for(std::size_t i=0; i<templ_row.expr.size(); ++i)
      {
        if(i>0)
          out << "+";
        out << from_expr(ns, "", v[row][elm].c[i]) << " * "
            << from_expr(ns, "", templ_row.expr[i].first);
      }
      out << std::endl;
    }
  }
}

void lexlinrank_domaint::output_domain(
  std::ostream &out,
  const namespacet &ns) const
{
  for(std::size_t row=0; row<templ.size(); row++)
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

    for(std::size_t i=0; i<templ_row.expr.size(); ++i)
    {
      if(i>0)
        out << "+";
      out << "c!" << row << "$" << i << " * "
          << from_expr(ns, "", templ_row.expr[i].first);
    }
    out << std::endl;
  }
}

void lexlinrank_domaint::project_on_vars(
  valuet &value,
  const var_sett &vars,
  exprt &result)
{
  // don't do any projection
  const templ_valuet &v=static_cast<const templ_valuet &>(value);
  assert(v.size()==templ.size());
  exprt::operandst c; // c is the conjunction of all rows
  c.reserve(templ.size());
  for(std::size_t row=0; row<templ.size(); ++row)
  {
    assert(templ[row].kind==LOOP);

    if(is_row_value_false(v[row]))
    {
      // (g=> false)
      c.push_back(
        implies_exprt(
          and_exprt(templ[row].pre_guard, templ[row].post_guard),
          false_exprt()));
    }
    else if(is_row_value_true(v[row]))
    {
      // (g=> true)
      c.push_back(
        implies_exprt(
          and_exprt(templ[row].pre_guard, templ[row].post_guard),
          true_exprt()));
    }
    else
    {
      exprt::operandst d; // d is the disjunction of lexicographic elements
      d.reserve(v[row].size());
      for(std::size_t elm=0; elm<v[row].size(); ++elm)
      {
        assert(v[row][elm].c.size()==templ[row].expr.size());
        assert(v[row][elm].c.size()>=1);

        // con is the constraints for a single element of the lexicography
        exprt::operandst con;
        con.reserve(1+v[row].size()-(elm+1));

        exprt sum=mult_exprt(
          v[row][elm].c[0],
          minus_exprt(
            templ[row].expr[0].first,
            templ[row].expr[0].second));

        for(std::size_t i=1; i<v[row][elm].c.size(); ++i)
        {
          sum=plus_exprt(
            sum,
            mult_exprt(
              v[row][elm].c[i],
              minus_exprt(
                templ[row].expr[i].first,
                templ[row].expr[i].second)));
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
              templ[row].expr[0].first,
              templ[row].expr[0].second));

          for(std::size_t i=1; i<v[row][elm2].c.size(); ++i)
          {
            sum2=plus_exprt(
              sum2,
              mult_exprt(
                v[row][elm2].c[i],
                minus_exprt(
                  templ[row].expr[i].first,
                  templ[row].expr[i].second)));
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
          and_exprt(templ[row].pre_guard, templ[row].post_guard),
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
    if(v.kind==LOOP)
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

  for(const auto &v : var_specs)
  {
    if(v.kind!=LOOP)
      continue;
    preg.push_back(v.pre_guard);
    postg.push_back(v.post_guard);
    exprt vpost=v.var; // copy
    rename(vpost);
    templ_row.expr.push_back(std::pair<exprt, exprt>(v.var, vpost));
  }

  templ_row.pre_guard=conjunction(preg);
  templ_row.post_guard=conjunction(postg);
}

bool lexlinrank_domaint::is_row_value_false(
  const row_valuet & row_value) const
{
  assert(row_value.size()>=1);
  assert(row_value[0].c.size()>=1);
  return row_value[0].c[0].get(ID_value)==ID_false;
}

bool lexlinrank_domaint::is_row_element_value_false(
  const row_value_elementt & row_value_element) const
{
  assert(false);
  assert(row_value_element.c.size()>=1);
  return row_value_element.c[0].get(ID_value)==ID_false;
}

bool lexlinrank_domaint::is_row_value_true(const row_valuet & row_value) const
{
  assert(row_value.size()>=1);
  assert(row_value[0].c.size()>=1);
  return row_value[0].c[0].get(ID_value)==ID_true;
}

bool lexlinrank_domaint::is_row_element_value_true(
  const row_value_elementt & row_value_element) const
{
  assert(false);
  assert(row_value_element.c.size()>=1);
  return row_value_element.c[0].get(ID_value)==ID_true;
}

void lexlinrank_domaint::add_element(
  const rowt &row,
  templ_valuet &value)
{
  value[row].push_back(row_value_elementt());
  for(unsigned i=0; i<value[row].size(); i++)
  {
    value[row][i].c.resize(1);
    value[row][i].c[0]=false_exprt();
  }
}
