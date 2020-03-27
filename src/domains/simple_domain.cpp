/*******************************************************************\

Module: Generic simple abstract domain class

Author: Viktor Malik

\*******************************************************************/

/// \file
/// Generic simple abstract domain class
/// Designed to work with the generic simple strategy solver located in
/// strategy_solver_simplet.
/// Implements a default behaviour for a number of methods that are common for
/// multiple simple abstract domains.

#include "simple_domain.h"
#include "util.h"
#include <util/find_symbols.h>
#include <algorithm>

/// Get pre constraints from the given value.
/// Default behaviour: make a conjunction of row pre constraints for each
/// template row.
exprt simple_domaint::to_pre_constraints(const valuet &value)
{
  exprt::operandst c;
  for(rowt row=0; row<templ.size(); row++)
  {
    c.push_back(get_row_pre_constraint(row, value));
  }
  return conjunction(c);
}

/// Get row pre constraint for the given row from the given abstract value.
/// Default row pre constraint:
///   pre_guard => row_value_expression
exprt simple_domaint::get_row_pre_constraint(rowt row, const valuet &value)
{
  // For exit variables the result is true
  if(templ[row].guards.kind==guardst::OUT ||
     templ[row].guards.kind==guardst::OUTL)
    return true_exprt();

  auto row_expr=get_row_value_constraint(row, value);
  return implies_exprt(templ[row].guards.pre_guard, row_expr);
}

/// Get post constraints from the given value.
/// Since it is necessary to know which constraint was satisfied by the SMT
/// solver, they are stored in a vector cond_exprs and the strategy solver
/// makes a disjunction of them and passes it to the SMT solver.
/// Post constraints are typically negations of row expressions (to solve the
/// "exists forall" problem).
/// Default behaviour: each template row has its own post constraint.
void simple_domaint::make_not_post_constraints(
  const valuet &value,
  exprt::operandst &cond_exprs)
{
  for(rowt row=0; row<templ.size(); row++)
  {
    strategy_value_exprs.push_back(templ[row].expr->get_row_exprs());
    for(auto &row_var : strategy_value_exprs[row])
      rename(row_var);
    cond_exprs.push_back(get_row_post_constraint(row, value));
  }
}

/// Get row post constraint for the given row from the given abstract value.
/// Default post constraint:
///   aux_expr && !(post_guard => row_value_expression)
exprt simple_domaint::get_row_post_constraint(rowt row, const valuet &value)
{
  exprt row_post_constraint;
  if(templ[row].guards.kind==guardst::IN)
    row_post_constraint=true_exprt();
  else
  {
    auto row_expr=get_row_value_constraint(row, value);
    row_post_constraint=implies_exprt(templ[row].guards.post_guard, row_expr);
  }

  if(templ[row].guards.kind==guardst::LOOP)
    rename(row_post_constraint);

  return and_exprt(templ[row].guards.aux_expr, not_exprt(row_post_constraint));
}

/// Get value constraint for the given row.
/// Default is the row expression of the value.
exprt simple_domaint::get_row_value_constraint(rowt row, const valuet &value)
{
  return value.get_row_expr(row, templ[row]);
}

/// Print the template to the given output stream
void simple_domaint::templatet::output(
  std::ostream &out,
  const namespacet &ns) const
{
  for(rowt row=0; row<size(); row++)
  {
    (*this)[row].guards.output(out, ns);
    out << row << ": ";
    (*this)[row].expr->output(out, ns);
  }
}

/// Output the domain (its template)
/// Default behaviour: output template.
void simple_domaint::output_domain(
  std::ostream &out,
  const namespacet &ns) const
{
  templ.output(out, ns);
}

/// Output the given abstract value in this domain.
/// Default behavior: for each template row, print the row value expression.
void simple_domaint::output_value(
  std::ostream &out,
  const domaint::valuet &value,
  const namespacet &ns) const
{
  auto &simple_value=dynamic_cast<const valuet &>(value);
  for(rowt row=0; row<templ.size(); row++)
  {
    templ[row].guards.output(out, ns);
    out << from_expr(ns, "", simple_value.get_row_expr(row, templ[row]))
        << std::endl;
  }
}

/// Project invariant (abstract value) onto a set of variables.
/// Default behaviour: result is a conjunction of expressions of all template
/// row such that all symbols occurring in the row expression are in vars
/// Here, the projected expression is:
///   pre_constraint       for LOOP rows
///   value_row_expression for IN and OUT rows
void simple_domaint::project_on_vars(
  domaint::valuet &value,
  const var_sett &vars,
  exprt &result)
{
  auto &simple_value=dynamic_cast<valuet &>(value);
  exprt::operandst c;
  for(rowt row=0; row<templ.size(); row++)
  {
    std::set<symbol_exprt> symbols;
    for(auto &row_expr : templ[row].expr->get_row_exprs())
    {
      std::set<symbol_exprt> row_expr_symbols;
      find_symbols(row_expr, row_expr_symbols);
      symbols.insert(row_expr_symbols.begin(), row_expr_symbols.end());
    }

    // If any of the symbols is not in vars and vars is not empty, continue
    if(!vars.empty() && std::any_of(
      symbols.begin(), symbols.end(),
      [&vars](const symbol_exprt &s)
      {
        return vars.find(s)==vars.end();
      }))
      continue;

    if(templ[row].guards.kind==guardst::LOOP)
      c.push_back(get_row_pre_constraint(row, simple_value));
    else
      c.push_back(get_row_value_constraint(row, simple_value));
  }

  result=conjunction(c);
}

/// Return the loop guard for the given template row.
/// By default, it is the second conjunct in the row pre-guard.
exprt simple_domaint::get_current_loop_guard(rowt row)
{
  if(templ[row].guards.pre_guard.id()==ID_and)
    return to_and_expr(templ[row].guards.pre_guard).op1();

  return true_exprt();
}

/// Restrict the template to the given symbolic path.
/// Default behaviour: for each template row, add all loop guards from the
/// symbolic path (except for the loop guard corresponding to the row)
/// to aux_expr.
void simple_domaint::restrict_to_sympath(const symbolic_patht &sympath)
{
  for(rowt row=0; row<templ.size(); row++)
  {
    const exprt c=sympath.get_expr(get_current_loop_guard(row));
    templ[row].guards.aux_expr=and_exprt(templ[row].guards.aux_expr, c);
  }
}

/// Restrict template to any other paths than those specified.
void simple_domaint::eliminate_sympaths(
  const std::vector<symbolic_patht> &sympaths)
{
  for(rowt row=0; row<templ.size(); row++)
  {
    exprt::operandst paths;
    for(auto &sympath : sympaths)
    {
      const exprt path_expr=sympath.get_expr(get_current_loop_guard(row));
      paths.push_back(path_expr);
    }
    templ[row].guards.aux_expr=paths.empty()
                               ? static_cast<exprt>(true_exprt())
                               : not_exprt(disjunction(paths));
  }
}

/// Undo the last symbolic path restriction
/// Default behaviour: for each template row, remove the second conjunct
/// from aux_expr.
void simple_domaint::undo_sympath_restriction()
{
  for(auto &row : templ)
  {
    if(row.guards.aux_expr.id()==ID_and)
      row.guards.aux_expr=to_and_expr(row.guards.aux_expr).op0();
  }
}

/// Remove all symbolic path restrictions.
/// Default behaviour: for each template row, clear aux_expr.
void simple_domaint::remove_all_sympath_restrictions()
{
  for(auto &row : templ)
    row.guards.aux_expr=true_exprt();
}
