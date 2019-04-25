/*******************************************************************\

Module: May-alias analysis for a single function

Author: Viktor Malik, imalik@fit.vutbr.cz

\*******************************************************************/

/// \file
/// May-alias analysis for a single function

#include "may_alias_analysis.h"

void may_alias_domaint::transform(
  ai_domain_baset::locationt from,
  ai_domain_baset::locationt to,
  ai_baset &ai,
  const namespacet &ns)
{
  if(from->is_assign())
  {
    const code_assignt &code_assign=to_code_assign(from->code);

    const exprt lhs_deref=dereference(code_assign.lhs(), ns);
    const exprt rhs_deref=dereference(code_assign.rhs(), ns);

    std::set<irep_idt> aliases;
    get_rhs_aliases(rhs_deref, aliases);
    assign_lhs_aliases(lhs_deref, aliases);
  }
}

bool may_alias_domaint::merge(
  const may_alias_domaint &other,
  ai_domain_baset::locationt from,
  ai_domain_baset::locationt to)
{
  bool changed=false;

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
