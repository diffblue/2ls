/*******************************************************************\

Module: Analysis of potential relations among expressions.
        Computes which expressions (mainly symbols) occur in the same
        expression/statement and therefore there may be a relation
        between them. This information can be later used to create
        a more precise analysis template.

Author: Viktor Malik, viktor.malik@gmail.com

\*******************************************************************/

/// \file
/// Analysis of potential relations among expressions.
/// Computes which expressions (mainly symbols) occur in the same
/// expression/statement and therefore there may be a relation between them.
/// This information can be later used to create a more precise analysis
/// template.

#include "expression_dependence.h"

#include "dynamic_objects.h"
#include "ssa_dereference.h"

#include <algorithm>

/// Recursively collect all expressions of interest.
void expression_dependence_domaint::collect_exprs_rec(const exprt &expr,
                                                      const namespacet &ns,
                                                      std::set<exprt> &result)
{
  if(is_symbol_struct_member(expr, ns))
  {
    result.insert(expr);

    ssa_objectt object(expr, ns);
    if(!object)
      return;
    if(may_ignore(object))
    {
      result.erase(expr);
      return;
    }

    result.insert(object.symbol_expr());

    auto &type = ns.follow(expr.type());
    if(type.id() == ID_struct)
    {
      for(auto &comp : to_struct_type(type).components())
      {
        collect_exprs_rec(
          member_exprt(object.symbol_expr(), comp.get_name(), comp.type()),
          ns,
          result);
      }
    }
  }
  else if(expr.id() == ID_index)
  {
    result.insert(expr);
    // For array access, add the array, too
    auto &arr = to_index_expr(expr).array();
    if(arr.id() == ID_symbol)
      result.insert(arr);
  }
  else
  {
    forall_operands(o_it, expr)
      collect_exprs_rec(*o_it, ns, result);
  }
}

/// Put all given expressions (and their existing dependencies) into
/// the same dependence set.
void expression_dependence_domaint::make_union(std::set<exprt> &exprs)
{
  if(exprs.empty())
    return;

  auto &first = *exprs.begin();
  for(auto it = std::next(exprs.begin()); it != exprs.end(); it = std::next(it))
    dep_sets.make_union(first, *it);
}

void expression_dependence_domaint::make_union(std::set<exprt> &exprs1,
                                               std::set<exprt> &exprs2)
{
  std::set<exprt> exprs(exprs1);
  exprs.insert(exprs2.begin(), exprs2.end());
  make_union(exprs);
}

void expression_dependence_domaint::transform(const irep_idt &,
                                              trace_ptrt trace_from,
                                              const irep_idt &,
                                              trace_ptrt trace_to,
                                              ai_baset &ai,
                                              const namespacet &ns)
{
  auto &SSA = dynamic_cast<expression_dependencet &>(ai).SSA;

  locationt from(trace_from->current_location());
  if(from->is_assign())
  {
    if(SSA.dynamic_objects.have_objects(*from))
      return;

    const exprt lhs =
      dereference(from->assign_lhs(), SSA.ssa_value_ai[from], "", ns, false);
    const exprt rhs =
      dereference(from->assign_rhs(), SSA.ssa_value_ai[from], "", ns, false);

    std::set<exprt> lhs_exprs;
    std::set<exprt> rhs_exprs;
    collect_exprs_rec(lhs, ns, lhs_exprs);
    collect_exprs_rec(rhs, ns, rhs_exprs);

    make_union(lhs_exprs, rhs_exprs);
    for(auto &cond : conditionals)
    {
      // If the assignment LHS is an array access and the condition that it
      // depends on contains just the accessed index, do not add the index into
      // dependent expressions. This is to avoid creating needless dependencies
      // as iterating through would always make the array contents dependent on
      // the index, which is almost never the case.
      if(cond.guard_exprs.size() == 1 && lhs.id() == ID_index &&
         same_var(to_index_expr(lhs).index(), *cond.guard_exprs.begin()))
        continue;

      make_union(lhs_exprs, cond.guard_exprs);
    }
  }
  else if(from->is_goto() || from->is_assume() || from->is_assert())
  {
    std::set<exprt> exprs;
    const exprt guard =
      dereference(from->condition(), SSA.ssa_value_ai[from], "", ns, false);
    collect_exprs_rec(guard, ns, exprs);
    make_union(exprs);

    // a conditional GOTO affects all expressions until its target loc
    if(from->is_goto() && !from->condition().is_true())
    {
      struct conditionalt cond;
      cond.guard_exprs = exprs;
      cond.end = from->get_target();
      // if there is an else branch (another forward GOTO just before the
      // target), all expressions until the end of the else branch are affected
      auto other_goto = --from->get_target();
      if(other_goto->is_goto() && !other_goto->is_backwards_goto())
        cond.end = other_goto->get_target();

      if(std::find(conditionals.begin(), conditionals.end(), cond) ==
         conditionals.end())
        conditionals.push_back(cond);
    }
  }

  if(from->is_backwards_goto())
    loop_end = from->location_number;
}

bool expression_dependence_domaint::merge(
  const expression_dependence_domaint &other,
  trace_ptrt trace_from,
  trace_ptrt trace_to)
{
  bool result = has_values.is_false() && !other.has_values.is_false();
  has_values = tvt::unknown();

  locationt from(trace_from->current_location());
  locationt to(trace_to->current_location());

  if(other.conditionals.size() > conditionals.size())
  {
    conditionals = other.conditionals;
    result = true;
  }
  while(!conditionals.empty() && conditionals.back().end == to)
  {
    conditionals.pop_back();
    result = true;
  }

  if(other.loop_end)
  {
    if(!(from->is_goto() && to->location_number > other.loop_end))
    {
      if(loop_end != other.loop_end)
      {
        loop_end = other.loop_end;
        result = true;
      }
    }
  }

  if(!loop_end)
    return result;

  for(auto &a : other.dep_sets)
  {
    for(auto &b : other.dep_sets)
    {
      if(other.dep_sets.same_set(a, b) && !dep_sets.same_set(a, b))
      {
        dep_sets.make_union(a, b);
        result = true;
      }
    }
  }
  return result;
}

void expression_dependence_domaint::output(std::ostream &out,
                                           const ai_baset &ai,
                                           const namespacet &ns) const
{
  out << "Loop: " << loop_end << "\n";
  for(const exprt &e : dep_sets)
  {
    auto n = dep_sets.get_number(e);
    if(n.has_value())
      out << "    " << dep_sets.find_number(*n) << ": " << from_expr(ns, "", e)
          << "\n";
  }
}

bool expression_dependence_domaint::may_ignore(const ssa_objectt &ssa_object)
{
  std::string id = id2string(ssa_object.get_identifier());
  if(id.find("__VERIFIER_nondet") != std::string::npos)
    return true;
  if(id.find("dynamic_object$") != std::string::npos &&
     id.find("$pad") != std::string::npos)
    return true;

  return false;
}

const expression_dependence_domaint &
expression_dependencet::get_deps_for_ssa_expr(const exprt &expr,
                                              const local_SSAt &SSA)
{
  if(expr.id() == ID_symbol)
  {
    auto expr_id = to_symbol_expr(expr).get_identifier();
    auto loc = isdigit(id2string(expr_id).back())
                 ? SSA.get_loc_with_symbol_def(to_symbol_expr(expr))
                 : (SSA.nodes.end()--)->location;
    return (*this)[loc];
  }
  else
    assert(false);
}

void expression_dependencet::initialize(
  const irep_idt &function_id,
  const goto_functionst::goto_functiont &goto_function)
{
  ait<expression_dependence_domaint>::initialize(function_id, goto_function);
  forall_goto_program_instructions(i_it, goto_function.body)
    get_state(i_it).make_bottom();
}
