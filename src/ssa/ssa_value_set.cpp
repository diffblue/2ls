/*******************************************************************\

Module: A flow-insensitive value set analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "ssa_value_set.h"

/*******************************************************************\

Function: ssa_value_domaint::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_value_domaint::transform(
  locationt from,
  locationt to,
  ai_baset &ai,
  const namespacet &ns)
{
  if(from->is_assign())
  {
    const code_assignt &assignment=to_code_assign(from->code);
    assign_lhs_rec(assignment.lhs(), assignment.rhs(), ns);
  }
  else if(from->is_goto())
  {
    // Perhaps look at condition, for stuff like
    // p!=0 or the like.
  }
  else if(from->is_decl())
  {
    const code_declt &code_decl=to_code_decl(from->code);
    assign_lhs_rec(code_decl.symbol(), nil_exprt(), ns);
  }
  else if(from->is_function_call())
  {
    const code_function_callt &code_function_call=
      to_code_function_call(from->code);

    // functions may alter state almost arbitrarily:
    // * any global-scoped variables
    // * any dirty locals
    
    #if 0
    for(objectst::const_iterator
        o_it=ssa_objects.dirty_locals.begin();
        o_it!=ssa_objects.dirty_locals.end(); o_it++)
      assign(*o_it, it, ns);

    for(objectst::const_iterator
        o_it=ssa_objects.globals.begin();
        o_it!=ssa_objects.globals.end(); o_it++)
      assign(*o_it, it, ns);
    #endif

    // the call might come with an assignment
    if(code_function_call.lhs().is_not_nil())
      assign_lhs_rec(code_function_call.lhs(), nil_exprt(), ns);
  }
  else if(from->is_dead())
  {
    const code_deadt &code_dead=to_code_dead(from->code);
    assign_lhs_rec(code_dead.symbol(), nil_exprt(), ns);
  }
}

/*******************************************************************\

Function: ssa_value_domaint::assign_lhs_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_value_domaint::assign_lhs_rec(
  const exprt &lhs,
  const exprt &rhs,
  const namespacet &ns,
  bool add)
{
  // is the lhs an object?
  if(is_symbol_struct_member(lhs, ns))
  {
    const typet &lhs_type=ns.follow(lhs.type());
    
    if(lhs_type.id()==ID_struct)
    {
      // Are we assigning an entire struct?
      // If so, need to split into pieces, recursively.
    
      const struct_typet &struct_type=to_struct_type(lhs_type);
      const struct_typet::componentst &components=struct_type.components();
      
      for(struct_typet::componentst::const_iterator
          it=components.begin();
          it!=components.end();
          it++)
      {
        member_exprt new_lhs(lhs, it->get_name(), it->type());
        member_exprt new_rhs(rhs, it->get_name(), it->type());
        assign_lhs_rec(new_lhs, new_rhs, ns, add); // recursive call
      }
      
      return; // done
    }

    // object?
    ssa_objectt ssa_object(lhs, ns);
    
    if(ssa_object)
    {
      valuest &lhs_values=value_map[ssa_object];
      lhs_values.clear();
      assign_rhs_rec(lhs_values, rhs, ns);
      if(lhs_values.empty())
        value_map.erase(ssa_object);
    }

    return; // done
  }
  else if(lhs.id()==ID_typecast)
  {
    assign_lhs_rec(to_typecast_expr(lhs).op(), rhs, ns, add);
  }
  else if(lhs.id()==ID_if)
  {
    assign_lhs_rec(to_if_expr(lhs).true_case(), rhs, ns, true);
    assign_lhs_rec(to_if_expr(lhs).false_case(), rhs, ns, true);
  }
  else if(lhs.id()==ID_index)
  {
    assign_lhs_rec(to_index_expr(lhs).array(), rhs, ns, true);
  }
  else if(lhs.id()==ID_dereference)
  {
    valuest tmp;
    assign_rhs_rec(tmp, to_dereference_expr(lhs).pointer(), ns, false);
    for(valuest::value_sett::const_iterator
        it=tmp.value_set.begin();
        it!=tmp.value_set.end();
        it++)
    {
      assign_rhs_rec(value_map[*it], rhs, ns);
    }
  }
  else if(lhs.id()==ID_member)
  {
    #if 0
    // non-flattened struct or union member
    const member_exprt &member_expr=to_member_expr(lhs);
    assign(member_expr.struct_op(), loc, ns);
    #endif
  }
  else if(lhs.id()==ID_complex_real || lhs.id()==ID_complex_imag)
  {
    #if 0
    assert(lhs.operands().size()==1);
    assign(lhs.op0(), loc, ns);
    #endif
  }
}

/*******************************************************************\

Function: ssa_value_domaint::assign_rhs_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_value_domaint::assign_rhs_rec(
  valuest &dest,
  const exprt &rhs,
  const namespacet &ns,
  bool offset) const
{
  if(rhs.id()==ID_address_of)
  {
    const exprt &op=to_address_of_expr(rhs).object();
  
    ssa_objectt ssa_object(op, ns);
  
    if(ssa_object)
    {
      dest.value_set.insert(ssa_object);
      if(offset) dest.offset=true;
    }
  }
  else if(rhs.id()==ID_constant)
  {
    if(to_constant_expr(rhs).get_value()==ID_NULL)
    {
      dest.null=true;
    }
  }
  else if(rhs.id()==ID_if)
  {
    assign_rhs_rec(dest, to_if_expr(rhs).true_case(), ns, offset);
    assign_rhs_rec(dest, to_if_expr(rhs).false_case(), ns, offset);
  }
  else if(rhs.id()==ID_typecast)
  {
    assign_rhs_rec(dest, to_typecast_expr(rhs).op(), ns, offset);
  }
  else if(rhs.id()==ID_dereference)
  {
    valuest tmp;
    assign_rhs_rec(tmp, to_dereference_expr(rhs).pointer(), ns, false);
    for(valuest::value_sett::const_iterator
        it=tmp.value_set.begin();
        it!=tmp.value_set.end();
        it++)
    {
      value_mapt::const_iterator m_it=value_map.find(*it);
      if(m_it!=value_map.end())
        dest.merge(m_it->second);
    }
  }
  else
  {
    // object?
  
    ssa_objectt ssa_object(rhs, ns);
  
    if(ssa_object)
    {
      value_mapt::const_iterator m_it=value_map.find(ssa_object);
      if(m_it!=value_map.end())
        dest.merge(m_it->second);
    }
    else
    {
      forall_operands(it, rhs)
        assign_rhs_rec(dest, *it, ns, true);
    }
  }
}

/*******************************************************************\

Function: ssa_value_domaint::valuest::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_value_domaint::valuest::output(
  std::ostream &out,
  const namespacet &ns) const
{
  if(offset) out << " offset";
  if(null) out << " null";
  if(unknown) out << " unknown";
  if(integer_address) out << " integer_address";

  for(value_sett::const_iterator it=value_set.begin();
      it!=value_set.end();
      it++)
    out << ' ' << '&' << it->get_identifier();
}

/*******************************************************************\

Function: ssa_value_domaint::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_value_domaint::output(
  std::ostream &out,
  const ai_baset &ai,
  const namespacet &ns) const
{
  for(value_mapt::const_iterator
      v_it=value_map.begin();
      v_it!=value_map.end();
      v_it++)
  {
    out << v_it->first.get_identifier() << ':';
    v_it->second.output(out, ns);
    out << '\n';
  }
}

/*******************************************************************\

Function: ssa_value_domaint::valuest::merge

  Inputs:

 Outputs: Return true if "this" has changed.

 Purpose:

\*******************************************************************/

bool ssa_value_domaint::valuest::merge(const valuest &src)
{
  bool result=false;

  // bits
  if(src.offset && !offset) { offset=true; result=true; }
  if(src.null && !null) { null=true; result=true; }
  if(src.unknown && !unknown) { unknown=true; result=true; }
  if(src.integer_address && !integer_address) { integer_address=true; result=true; }

  // value set
  unsigned old_size=value_set.size();
  value_set.insert(src.value_set.begin(), src.value_set.end());
  if(old_size!=value_set.size()) result=true;

  return result;  
}

/*******************************************************************\

Function: ssa_value_domaint::merge

  Inputs:

 Outputs: Return true if "this" has changed.

 Purpose:

\*******************************************************************/

bool ssa_value_domaint::merge(
  const ssa_value_domaint &other,
  locationt from,
  locationt to)
{
  value_mapt::iterator v_it=value_map.begin();
  const value_mapt &new_value_map=other.value_map;
  bool result=false;
  
  for(value_mapt::const_iterator
      it=new_value_map.begin();
      it!=new_value_map.end();
      ) // no it++
  {
    if(v_it==value_map.end() || it->first<v_it->first)
    {
      value_map.insert(v_it, *it);
      result=true;
      it++;
      continue;
    }
    else if(v_it->first<it->first)
    {
      v_it++;
      continue;
    }
    
    assert(v_it->first==it->first);
      
    if(v_it->second.merge(it->second))
      result=true;

    v_it++;
    it++;
  }
  
  return result;
}
