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
  const ssa_objectst &ssa_objects=
    static_cast<const ssa_value_ait &>(ai).ssa_objects;

  if(from->is_assign())
  {
    const code_assignt &assignment=to_code_assign(from->code);
    assign(assignment.lhs(), assignment.rhs(), ssa_objects, ns);
  }
  else if(from->is_goto())
  {
  }
  else if(from->is_decl())
  {
    const code_declt &code_decl=to_code_decl(from->code);
    assign(code_decl.symbol(), nil_exprt(), ssa_objects, ns);
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

    // the call might come with an assignment
    if(code_function_call.lhs().is_not_nil())
      assign(code_function_call.lhs(), it, ns);
    #endif
  }
  else if(from->is_dead())
  {
    const code_deadt &code_dead=to_code_dead(from->code);
    assign(code_dead.symbol(), nil_exprt(), ssa_objects, ns);
  }
}

/*******************************************************************\

Function: ssa_value_domaint::assign

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_value_domaint::assign(
  const exprt &lhs,
  const exprt &rhs,
  const ssa_objectst &ssa_objects,
  const namespacet &ns)
{
  // is the lhs an object?
  if(is_symbol_or_deref_struct_member(lhs, ns))
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
        assign(new_lhs, new_rhs, ssa_objects, ns); // recursive call
      }
      
      return; // done
    }

    #if 0    
    // this might alias all sorts of stuff
    for(std::set<ssa_objectt>::const_iterator
        o_it=ssa_objects.objects.begin();
        o_it!=ssa_objects.objects.end();
        o_it++)
    {
      if(ssa_may_alias(o_it->get_expr(), lhs, ns))
        assign(*o_it, loc, ns);
    }    
    #endif

    return; // done
  }

  #if 0
  if(lhs.id()==ID_typecast)
  {
    assign(to_typecast_expr(lhs).op(), loc, ns);
  }
  else if(lhs.id()==ID_if)
  {
    assign(to_if_expr(lhs).true_case(), loc, ns);
    assign(to_if_expr(lhs).false_case(), loc, ns);
  }
  else if(lhs.id()==ID_index)
  {
    assign(to_index_expr(lhs).array(), loc, ns);
  }
  else if(lhs.id()==ID_member)
  {
    // non-flattened struct or union member
    const member_exprt &member_expr=to_member_expr(lhs);
    assign(member_expr.struct_op(), loc, ns);
  }
  else if(lhs.id()==ID_complex_real || lhs.id()==ID_complex_imag)
  {
    assert(lhs.operands().size()==1);
    assign(lhs.op0(), loc, ns);
  }
  #endif
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
    out << ' ' << it->get_identifier();
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
}

