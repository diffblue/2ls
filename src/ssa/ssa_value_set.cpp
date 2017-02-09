/*******************************************************************\

Module: A flow-insensitive value set analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

//#define DEBUG

#ifdef DEBUG
#include <iostream>
#endif

#include <util/pointer_offset_size.h>
#include <algorithm>

#include "ssa_value_set.h"
#include "ssa_dereference.h"

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
    exprt lhs_deref=dereference(assignment.lhs(), *this, "", ns);
    exprt rhs_deref=dereference(assignment.rhs(), *this, "", ns);
    assign_lhs_rec(lhs_deref, rhs_deref, ns);
  }
  else if(from->is_goto())
  {
    // Perhaps look at condition, for stuff like
    // p!=0 or the like.
    //exprt cond_deref=dereference(from->guard, *this, "", ns);
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

    for (auto &argument : code_function_call.arguments())
    {
      exprt arg = argument;
      while (arg.type().id() == ID_pointer)
      {
        if (arg.id() == ID_symbol)
        {
          const typet &pointed_type = ns.follow(arg.type().subtype());
          symbol_exprt pointed_obj = symbol_exprt(
              id2string(to_symbol_expr(arg).get_identifier()) + "'obj",
              pointed_type);
          pointed_obj.type().set("#dynamic", true);

          assign_lhs_rec(arg, address_of_exprt(pointed_obj), ns, true);

          arg = pointed_obj;
        }
        else if (arg.id() == ID_address_of)
        {
          arg = to_address_of_expr(arg).object();
        }
      }
    }

    // the call might come with an assignment
    if(code_function_call.lhs().is_not_nil())
    {
      exprt lhs_deref=dereference(code_function_call.lhs(), *this, "", ns);
      assign_lhs_rec(lhs_deref, nil_exprt(), ns);
    }

    // the assignment of return value might be in next instruction
    if (to->is_assign() && to_code_assign(to->code).rhs().id() == ID_symbol)
    {
      const symbol_exprt &return_value = to_symbol_expr(to_code_assign(to->code).rhs());
      if (return_value.type().id() == ID_pointer &&
          return_value.get_identifier() ==
          id2string(to_symbol_expr(code_function_call.function()).get_identifier()) +
          "#return_value")
      {
        const typet &pointed_type = ns.follow(return_value.type().subtype());
        symbol_exprt pointed_obj = symbol_exprt(
            id2string(return_value.get_identifier()) + "'obj",
            pointed_type);
        pointed_obj.type().set("#dynamic", true);

        assign_lhs_rec(return_value, address_of_exprt(pointed_obj), ns);
      }
    }
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
  #ifdef DEBUG
  std::cout << "assign_lhs_rec lhs: " << from_expr(ns, "", lhs) << '\n';
  std::cout << "assign_lhs_rec rhs: " << from_expr(ns, "", rhs) << '\n';
  #endif
  
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

    if (ssa_object &&
        !(lhs.id() == ID_member && to_member_expr(lhs).compound().get_bool("#advancer")))
    {
      valuest tmp_values;
      assign_rhs_rec(tmp_values, rhs, ns, false, 0);

      valuest &lhs_values=value_map[ssa_object];

      if(add)
        lhs_values.merge(tmp_values);
      else
        lhs_values=tmp_values;

#if 0
      std::cout << "value_set: "; lhs_values.output(std::cout,ns); std::cout << std::endl;
#endif
  
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
//  assert(false); // should have been removed

    //not yet removed if there is an array inside a struct referenced by pointer
    assign_lhs_rec(to_dereference_expr(lhs).pointer(), rhs, ns, true);
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
  bool offset,
  unsigned alignment) const
{
#ifdef DEBUG
  std::cout << "assign_rhs_rec: " << from_expr(ns, "", rhs) << '\n';
#endif
  
  if(rhs.id()==ID_address_of)
  {
    const exprt &op=to_address_of_expr(rhs).object();
    assign_rhs_rec_address_of(dest, op, ns, offset, alignment);
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
    assign_rhs_rec(dest, to_if_expr(rhs).true_case(), ns, offset, alignment);
    assign_rhs_rec(dest, to_if_expr(rhs).false_case(), ns, offset, alignment);
  }
  else if(rhs.id()==ID_typecast)
  {
    assign_rhs_rec(dest, to_typecast_expr(rhs).op(), ns, offset, alignment);
  }
  else if(rhs.id()==ID_plus)
  {
    forall_operands(it, rhs)
    {
      if(it->type().id()==ID_pointer)
      {
        mp_integer pointer_offset=pointer_offset_size(it->type().subtype(), ns);
        if(pointer_offset<1) pointer_offset=1;
        unsigned a=merge_alignment(integer2long(pointer_offset), alignment);
        assign_rhs_rec(dest, *it, ns, true, a);
      }
    }
  }
  else if(rhs.id()==ID_minus)
  {
    assert(rhs.operands().size()==2);
    if(rhs.type().id()==ID_pointer)
    {
      mp_integer pointer_offset=pointer_offset_size(rhs.type().subtype(), ns);
      if(pointer_offset<1) pointer_offset=1;
      unsigned a=merge_alignment(integer2long(pointer_offset), alignment);
      assign_rhs_rec(dest, rhs.op0(), ns, true, a);
    }
  }
  else if(rhs.id()==ID_dereference)
  {
  //   std::cout << rhs.pretty() << std::endl;
  //   assert(false); // should have been removed

    //not yet removed if there is an array inside a struct referenced by pointer
    assign_rhs_rec(dest, rhs.op0(), ns, true, 1);
  }
  else
  {
    // object?
  
    ssa_objectt ssa_object(rhs, ns);

    if(ssa_object)
    {
      value_mapt::const_iterator m_it = value_map.find(ssa_object);

      if (m_it != value_map.end())
      {
        valuest tmp_values = m_it->second;
        if (offset) tmp_values.offset = true;
        tmp_values.alignment = merge_alignment(tmp_values.alignment, alignment);
        dest.merge(tmp_values);
      }
    }
    else
    {
      forall_operands(it, rhs)
        assign_rhs_rec(dest, *it, ns, true, 1);
    }
  }
}

/*******************************************************************\

Function: ssa_value_domaint::assign_rhs_rec_address_of

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_value_domaint::assign_rhs_rec_address_of(
  valuest &dest,
  const exprt &rhs,
  const namespacet &ns,
  bool offset,
  unsigned alignment) const
{
  ssa_objectt ssa_object(rhs, ns);

  if(ssa_object)
  {
    dest.add_to_value_set(ssa_object);
    if(offset) dest.offset=true;
  }
  else if(rhs.id()==ID_if)
  {
    assign_rhs_rec_address_of(dest, to_if_expr(rhs).true_case(), ns, offset, alignment);
    assign_rhs_rec_address_of(dest, to_if_expr(rhs).false_case(), ns, offset, alignment);
  }
  else if(rhs.id()==ID_index)
  {
    unsigned a=alignment;

    if(!to_index_expr(rhs).index().is_zero())
    {
      offset=true;
      mp_integer pointer_offset=pointer_offset_size(rhs.type(), ns);
      if(pointer_offset<1) pointer_offset=1;
      a=merge_alignment(a, integer2long(pointer_offset));
    }

    assign_rhs_rec_address_of(dest, to_index_expr(rhs).array(), ns, offset, a);
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
  if(offset)
  {
    out << " offset";
    if(alignment!=0) out << "*" << alignment;
  }

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
  for (const ssa_objectt &v : src.value_set)
  {
    result = add_to_value_set(v) || result;
  }

  // alignment
  alignment=merge_alignment(alignment, src.alignment);

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

/*******************************************************************\

Function: ssa_value_domaint::valuest::add_to_value_set

  Inputs: SSA object to be added

 Outputs: True if 'this' has changed

 Purpose: Add given object to value set of this.
          If value set contains both advancer (abstracts all elements
          of the list except the first one) and object pointed by
          advancer pointer (abstracts the first element of the list),
          only advancer is preserved and #except_first is set to false.

\*******************************************************************/
bool ssa_value_domaint::valuest::add_to_value_set(ssa_objectt object)
{
  if (value_set.find(object) == value_set.end())
  {
    bool result = false;
    if (object.get_expr().get_bool("#advancer"))
    { // advancer is to be inserted - check if set already contains first object of corresponding
      // list
      const irep_idt corresp_object_id = object.get_expr().get("#object_id");

      auto it = std::find_if(value_set.begin(), value_set.end(),
                             [&corresp_object_id](const ssa_objectt &o)
                             {
                               return o.get_identifier() == corresp_object_id;
                             });

      if (it != value_set.end())
      {
        value_set.erase(it);
        object.set_flag("#except_first", false);
        result = true;
      }
    }
    else if (id2string(object.get_identifier()).find("'obj") != std::string::npos)
    { // pointed object is to be inserted - check if set already contains corresponding advancer
      const irep_idt object_id = object.get_identifier();

      auto it = std::find_if(value_set.begin(), value_set.end(),
                             [&object_id](const ssa_objectt &o)
                             {
                               return id2string(o.get_identifier()).find(id2string(object_id)) !=
                                      std::string::npos &&
                                      id2string(o.get_identifier()).find("'adv") !=
                                      std::string::npos;
                             });

      if (it != value_set.end())
      {
        ssa_objectt new_advancer(*it);
        new_advancer.set_flag("#except_first", false);
        value_set.erase(it);
        value_set.insert(new_advancer);
        return false;
      }
    }

    auto inserted = value_set.insert(object);
    return result || inserted.second;
  }
  return false;
}

/*******************************************************************\

Function: ssa_value_ait::initialize

  Inputs: GOTO function

 Outputs:

 Purpose: Initialize value sets for pointer parameters and pointer-typed
          fields of objects pointed by parameters.

\*******************************************************************/
void ssa_value_ait::initialize(const goto_functionst::goto_functiont &goto_function)
{
  ait<ssa_value_domaint>::initialize(goto_function);

  // Initialize value sets for pointer parameters

  if (!goto_function.type.parameters().empty())
  {
    locationt e = goto_function.body.instructions.begin();
    ssa_value_domaint &entry = operator[](e);

    for (auto &param : goto_function.type.parameters())
    {
      const symbol_exprt param_expr(param.get_identifier(), param.type());
      assign_ptr_param_rec(param_expr, entry);
    }

  }
}

/*******************************************************************\

Function: ssa_value_ait::assign_ptr_param_rec

  Inputs: Expression to be initialized and entry record of value set analysis

 Outputs:

 Purpose: Initialize value set for the given expression and recursively for all
          structure members and all pointed objects.
          Pointer-typed variable p initially points to abstract object p'obj.
          Pointer-typed field of structure initially points to advancer.

\*******************************************************************/
void ssa_value_ait::assign_ptr_param_rec(const exprt &expr, ssa_value_domaint &entry)
{
  const typet &type = ns.follow(expr.type());
  if (type.id() == ID_pointer)
  {
    if (expr.id() == ID_symbol)
    { // pointer variable
      const symbol_exprt pointed_expr(id2string(to_symbol_expr(expr).get_identifier()) + "'obj",
                                      type.subtype());
      assign(expr, pointed_expr, entry);
      assign_ptr_param_rec(pointed_expr, entry);
    }
    else if (expr.id() == ID_member)
    { // pointer member of a structure
      const member_exprt &member = to_member_expr(expr);
      ssa_objectt member_obj(member, ns);
      symbol_exprt member_dest(id2string(member_obj.get_identifier()) + "'adv",
                               type.subtype());
      member_dest.set("#advancer", true);
      // intially advancer abstracts all list members except first
      member_dest.set("#except_first", true);
      assert(member.compound().id() == ID_symbol);
      // set advancer object
      member_dest.set("#object_id", to_symbol_expr(member.compound()).get_identifier());
      member_dest.set("#member", member.get_component_name());
      assign(expr, member_dest, entry);
    }
  }
  else if (type.id() == ID_struct)
  { // split structure into fields
    for (auto &component : to_struct_type(type).components())
    {
      const member_exprt member(expr, component.get_name(), component.type());
      assign_ptr_param_rec(member, entry);
    }
  }
}

/*******************************************************************\

Function: ssa_value_ait::assign

  Inputs: Pointer variable src, pointed object dest and analysis entry.

 Outputs:

 Purpose: Insert object to value set of another object in the given entry.

\*******************************************************************/
void ssa_value_ait::assign(const exprt &src, const exprt &dest, ssa_value_domaint &entry)
{
  ssa_objectt src_obj(src, ns);
  ssa_objectt dest_obj(dest, ns);
  if (src_obj && dest_obj)
  {
    entry.value_map[src_obj].value_set.insert(dest_obj);
  }
}
