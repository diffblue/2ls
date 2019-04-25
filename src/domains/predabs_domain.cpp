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
#include <util/i2string.h>
#include <util/simplify_expr.h>
#include <langapi/languages.h>

#include "predabs_domain.h"
#include "util.h"

#define SYMB_COEFF_VAR "symb_coeff#"
#define COMPLEXITY_COUNTER_PREFIX "__CPROVER_CPLX_CNT_"

void predabs_domaint::initialize(valuet &value)
{
  templ_valuet &v=static_cast<templ_valuet&>(value);
  v.resize(templ.size());
  for(std::size_t row=0; row<templ.size(); ++row)
  {
    // start from top (we can only use a gfp solver for this domain)
    v[row]=false_exprt();
  }
}

const exprt predabs_domaint::initialize_solver(
  const local_SSAt &SSA,
  const exprt &precondition,
  template_generator_baset &template_generator)
{
  get_row_set(todo_preds);
  return true_exprt();
}


void predabs_domaint::solver_iter_init(valuet &value)
{
  e_it=todo_preds.begin();
}

bool predabs_domaint::has_something_to_solve()
{
  return (e_it==todo_preds.end());
}

std::vector<exprt> predabs_domaint::get_required_smt_values(size_t row)
{
  std::vector<exprt> r;
  return r;
}

void predabs_domaint::set_smt_values(std::vector<exprt> got_values, size_t row)
{
}

bool predabs_domaint::edit_row(const rowt &row, valuet &inv, bool improved)
{
  todo_notpreds.insert(*e_it);
  return true;
}

void predabs_domaint::post_edit()
{
  todo_preds.erase(e_it);
}

bool predabs_domaint::handle_unsat(valuet &value, bool improved)
{
  set_row_value(*e_it, true_exprt(), value);
  return true;
}

exprt predabs_domaint::make_permanent(valuet &value)
{
  exprt to_r=to_pre_constraints(value);
  todo_preds.insert(todo_notpreds.begin(), todo_notpreds.end());
  todo_notpreds.clear();
  return to_r;
}

/// pre_guard==> (row_value=> row_expr)
exprt predabs_domaint::get_row_constraint(
  const rowt &row,
  const row_valuet &row_value)
{
  assert(row<templ.size());
  kindt k=templ[row].kind;
  if(k==OUT || k==OUTL)
    return true_exprt();
  return implies_exprt(row_value, templ[row].expr);
}

/// pre_guard==> (row_value=> row_expr)
exprt predabs_domaint::get_row_pre_constraint(
  const rowt &row,
  const row_valuet &row_value)
{
  assert(row<templ.size());
  const template_rowt &templ_row=templ[row];
  kindt k=templ_row.kind;
  if(k==OUT || k==OUTL)
    return true_exprt();
  return implies_exprt(row_value, templ[row].expr);
}

/// pre_guard==> (row_value=> row_expr)
exprt predabs_domaint::get_row_pre_constraint(
  const rowt &row,
  const templ_valuet &value)
{
  assert(value.size()==templ.size());
  return get_row_pre_constraint(row, value[row]);
}

/// post_guard=> (row_value=> row_expr)
exprt predabs_domaint::get_row_post_constraint(
  const rowt &row,
  const row_valuet &row_value)
{
  assert(row<templ.size());
  const template_rowt &templ_row=templ[row];
  if(templ_row.kind==IN)
    return true_exprt();
  exprt c=implies_exprt(
    templ_row.post_guard,
    implies_exprt(row_value, templ[row].expr));
  if(templ_row.kind==LOOP)
    rename(c);
  return c;
}

/// post_guard=> (row_value=> row_expr)
exprt predabs_domaint::get_row_post_constraint(
  const rowt &row,
  const templ_valuet &value)
{
  assert(value.size()==templ.size());
  return get_row_post_constraint(row, value[row]);
}

/// /\_all_rows ( pre_guard==> (row_value=> row_expr) )
exprt predabs_domaint::to_pre_constraints(valuet &_value)
{
  assert(*e_it<templ.size());
  const template_rowt &templ_row=templ[*e_it];
  kindt k=templ_row.kind;
  if(k==OUT || k==OUTL)
    return true_exprt();
  return implies_exprt(true_exprt(), templ[*e_it].expr);
}

/// for all rows !(post_guard==> (row_value=> row_expr) ) to be connected
/// disjunctively
void predabs_domaint::make_not_post_constraints(
  valuet &_value,
  exprt::operandst &cond_exprs)
{
  predabs_domaint::templ_valuet &value=
    static_cast<predabs_domaint::templ_valuet &>(_value);
  assert(value.size()==templ.size());
  cond_exprs.resize(templ.size());

  exprt::operandst c;
  for(std::size_t row=0; row<templ.size(); row++)
  {
    cond_exprs[row]=and_exprt(
      templ[row].aux_expr,
      not_exprt(get_row_post_constraint(row, value)));
  }
}

predabs_domaint::row_valuet predabs_domaint::get_row_value(
  const rowt &row,
  const templ_valuet &value)
{
  assert(row<value.size());
  assert(value.size()==templ.size());
  return value[row];
}

void predabs_domaint::project_on_vars(
  valuet &value,
  const var_sett &vars,
  exprt &result)
{
  const templ_valuet &v=static_cast<const templ_valuet &>(value);

  assert(v.size()==templ.size());
  exprt::operandst c;
  for(std::size_t row=0; row<templ.size(); row++)
  {
    const template_rowt &templ_row=templ[row];

    std::set<symbol_exprt> symbols;
    find_symbols(templ_row.expr, symbols);

    bool pure=true;
    for(const auto &symbol : symbols)
    {
      if(vars.find(symbol)==vars.end())
      {
        pure=false;
        break;
      }
    }
    if(!pure)
      continue;

    const row_valuet &row_v=v[row];
    if(templ_row.kind==LOOP)
    {
      c.push_back(
        implies_exprt(
          templ_row.pre_guard,
          implies_exprt(row_v, templ_row.expr)));
    }
    else
    {
      c.push_back(implies_exprt(row_v, templ_row.expr));
    }
  }
  result=conjunction(c);
}

void predabs_domaint::set_row_value(
  const rowt &row,
  const predabs_domaint::row_valuet &row_value,
  valuet &_value)
{
  predabs_domaint::templ_valuet &value=
    static_cast<predabs_domaint::templ_valuet &>(_value);
  assert(row<value.size());
  assert(value.size()==templ.size());
  value[row]=row_value;
}

void predabs_domaint::output_value(
  std::ostream &out,
  const valuet &value,
  const namespacet &ns) const
{
  const templ_valuet &v=static_cast<const templ_valuet &>(value);
  for(std::size_t row=0; row<templ.size(); ++row)
  {
    const template_rowt &templ_row=templ[row];
    switch(templ_row.kind)
    {
    case LOOP:
      out << "(LOOP) [ " << from_expr(ns, "", templ_row.pre_guard) << " | ";
      out << from_expr(ns, "", templ_row.post_guard) << " | ";
      out << from_expr(ns, "", templ_row.aux_expr)
          << " ]===> " << std::endl << "       ";
      break;
    case IN: out << "(IN)   "; break;
    case OUT: case OUTL: out << "(OUT)  "; break;
    default: assert(false);
    }
    out << "( " << from_expr(ns, "", v[row]) << "==> " <<
       from_expr(ns, "", templ_row.expr) << " )" << std::endl;
  }
}

void predabs_domaint::output_domain(
  std::ostream &out,
  const namespacet &ns) const
{
  for(std::size_t row=0; row<templ.size(); ++row)
  {
    const template_rowt &templ_row=templ[row];
    switch(templ_row.kind)
    {
    case LOOP:
      out << "(LOOP) [ " << from_expr(ns, "", templ_row.pre_guard) << " | ";
      out << from_expr(ns, "", templ_row.post_guard) << " | ";
      out << from_expr(ns, "", templ_row.aux_expr)
          << " ]===> " << std::endl << "      ";
      break;
    case IN:
      out << "(IN)   ";
      out << from_expr(ns, "", templ_row.pre_guard)
          << "===> " << std::endl << "      ";
      break;
    case OUT: case OUTL:
      out << "(OUT)  ";
      out << from_expr(ns, "", templ_row.post_guard)
          << "===> " << std::endl << "      ";
      break;
    default: assert(false);
    }
    out << "( " << from_expr(ns, "", templ_row.expr) << ")" << std::endl;
  }
}

unsigned predabs_domaint::template_size()
{
  return templ.size();
}

predabs_domaint::template_rowt &predabs_domaint::add_template_row(
  const exprt& expr,
  const exprt& pre_guard,
  const exprt& post_guard,
  const exprt& aux_expr,
  kindt kind
  )
{
  templ.push_back(template_rowt());
  template_rowt &templ_row=templ.back();
  templ_row.expr=expr;
  // extend_expr_types(templ_row.expr);
  templ_row.pre_guard=pre_guard;
  templ_row.post_guard=post_guard;
  templ_row.aux_expr=aux_expr;
  templ_row.kind=kind;
  return templ_row;
}

void predabs_domaint::get_row_set(std::set<rowt> &rows)
{
  for(std::size_t i=0; i<templ.size(); ++i)
    rows.insert(i);
}
