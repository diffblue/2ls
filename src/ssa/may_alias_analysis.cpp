/*******************************************************************\

Module: May-alias analysis for a single function

Author: Viktor Malik, imalik@fit.vutbr.cz

\*******************************************************************/

/// \file
/// May-alias analysis for a single function

#include "may_alias_analysis.h"

void may_alias_domaint::transform(
  const irep_idt &from_function,
  trace_ptrt trace_from,
  const irep_idt &to_function,
  trace_ptrt trace_to,
  ai_baset &ai,
  const namespacet &ns)
{
  locationt from{trace_from->current_location()};

  if(from->is_assign())
  {
    const exprt lhs_deref=dereference(from->assign_lhs(), ns);
    const exprt rhs_deref=dereference(from->assign_rhs(), ns);

    std::set<irep_idt> aliases;
    get_rhs_aliases(rhs_deref, aliases);
    assign_lhs_aliases(lhs_deref, aliases);
  }
}

bool may_alias_domaint::merge(
  const may_alias_domaint &other,
  trace_ptrt trace_from,
  trace_ptrt trace_to)
{
  bool changed=has_values.is_false() && !other.has_values.is_false();

  // do union
  for(aliasest::const_iterator it=other.aliases.begin();
      it!=other.aliases.end(); it++)
  {
    irep_idt other_root=other.aliases.find(it);

    if(!aliases.same_set(*it, other_root))
    {
      aliases.make_union(*it, other_root);
      changed=true;
    }
  }

  return changed;
}

void may_alias_domaint::assign_lhs_aliases(
  const exprt &lhs,
  const std::set<irep_idt> &alias_set)
{
  if(lhs.type().id()==ID_pointer)
  {
    if(lhs.id()==ID_symbol)
    {
      irep_idt identifier=to_symbol_expr(lhs).get_identifier();

      aliases.isolate(identifier);

      for(const irep_idt &alias : alias_set)
      {
        aliases.make_union(identifier, alias);
      }
    }
  }
}

void may_alias_domaint::get_rhs_aliases(
  const exprt &rhs,
  std::set<irep_idt> &alias_set)
{
  if(rhs.id()==ID_symbol &&
     id2string(to_symbol_expr(rhs).get_identifier()).find("__CPROVER_")==
     std::string::npos)
  {
    irep_idt identifier=to_symbol_expr(rhs).get_identifier();
    alias_set.insert(identifier);

    for(aliasest::const_iterator it=aliases.begin();
        it!=aliases.end();
        it++)
      if(aliases.same_set(*it, identifier))
        alias_set.insert(*it);
  }
  else if(rhs.id()==ID_if)
  {
    get_rhs_aliases(to_if_expr(rhs).true_case(), alias_set);
    get_rhs_aliases(to_if_expr(rhs).false_case(), alias_set);
  }
  else if(rhs.id()==ID_typecast)
  {
    get_rhs_aliases(to_typecast_expr(rhs).op(), alias_set);
  }
}

const exprt may_alias_domaint::dereference(
  const exprt &expr,
  const namespacet &ns)
{
  exprt deref=symbolic_dereference(expr, ns);
  members_to_symbols(deref, ns);
  return deref;
}

void may_alias_domaint::members_to_symbols(exprt &expr, const namespacet &ns)
{
  ssa_objectt object(expr, ns);
  if(object)
    expr=object.symbol_expr();
  Forall_operands(it, expr)members_to_symbols(*it, ns);
}

void may_alias_analysist::initialize(
  const irep_idt &function_id,
  const goto_functionst::goto_functiont &goto_function)
{
  ait<may_alias_domaint>::initialize(function_id, goto_function);
  forall_goto_program_instructions(i_it, goto_function.body)
    get_state(i_it).make_bottom();
}
