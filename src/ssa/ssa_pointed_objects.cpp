/*******************************************************************\

Module: Library of functions for working with pointed objects

Author: Viktor Malik

\*******************************************************************/

/// \file
/// Library of functions for working with pointed objects

#include <util/c_types.h>

#include "ssa_pointed_objects.h"
#include "ssa_object.h"

const irep_idt level_str(const unsigned level, const irep_idt &suffix)
{
  return "#lvl_"+std::to_string(level)+"_"+id2string(suffix);
}

void copy_pointed_info(exprt &dest, const exprt &src, const unsigned max_level)
{
  if(max_level<pointed_level(src))
  {
    dest.set(ID_pointed, true);
    dest.set(ID_pointed_level, max_level+1);
    for(unsigned l=0; l<=max_level; ++l)
    {
      const irep_idt lvl_pointed_id=src.get(level_str(l, ID_pointer_id));
      dest.set(level_str(l, ID_pointer_id), lvl_pointed_id);
      const irep_idt lvl_pointed_subtype=
        src.get(level_str(l, ID_pointer_subtype));
      dest.set(level_str(l, ID_pointer_subtype), lvl_pointed_subtype);
      if(lvl_pointed_id==ID_symbol)
      {
        const irep_idt lvl_pointer_sym=src.get(level_str(l, ID_pointer_sym));
        dest.set(level_str(l, ID_pointer_sym), lvl_pointer_sym);
      }
      else
      {
        const irep_idt lvl_str=src.get(level_str(l, ID_pointer_compound));
        dest.set(level_str(l, ID_pointer_compound), lvl_str);
        const irep_idt lvl_ptr_field=src.get(level_str(l, ID_pointer_field));
        dest.set(level_str(l, ID_pointer_field), lvl_ptr_field);
      }
    }
  }
}

symbol_exprt pointed_object(const exprt &expr, const namespacet &ns)
{
  assert(expr.type().id()==ID_pointer);

  ssa_objectt ssa_object(expr, ns);
  if(ssa_object)
  {
    const typet &pointed_type=ssa_object.type().subtype();
    symbol_exprt pointed(
      id2string(ssa_object.get_identifier())+"'obj", ns.follow(pointed_type));
    pointed.set(ID_pointed, true);

    unsigned level=0;
    const exprt root_obj=ssa_object.get_root_object();
    if(root_obj.get_bool(ID_pointed))
    {
      level=pointed_level(root_obj);
      copy_pointed_info(pointed, root_obj, level-1);
    }

    pointed.set(ID_pointed_level, level+1);

    assert(root_obj.id()==ID_symbol);

    pointed.set(level_str(level, ID_pointer_id), ssa_object.get_expr().id());
    if(ssa_object.get_expr().id()==ID_symbol)
    {
      pointed.set(
        level_str(level, ID_pointer_sym),
        ssa_object.get_identifier());
    }
    else
    {
      assert(ssa_object.get_expr().id()==ID_member);
      const member_exprt member=to_member_expr(ssa_object.get_expr());
      assert(member.compound().id()==ID_symbol);
      pointed.set(
        level_str(level, ID_pointer_compound),
        to_symbol_expr(member.compound()).get_identifier());
      pointed.set(
        level_str(level, ID_pointer_field),
        member.get_component_name());
    }

    if(pointed_type.id()==ID_symbol)
    {
      pointed.set(
        level_str(level, ID_pointer_subtype),
        to_struct_tag_type(pointed_type).get_identifier());
    }

    return pointed;
  }
  else
    return symbol_exprt("ssa::nondet_symbol", expr.type().subtype());
}

const irep_idt pointer_root_id(const exprt &expr)
{
  assert(expr.get_bool(ID_pointed));
  unsigned max_level_index=expr.get_size_t(ID_pointed_level)-1;
  if(expr.get(level_str(max_level_index, ID_pointer_id))==ID_symbol)
    return expr.get(level_str(max_level_index, ID_pointer_sym));
  else
    return expr.get(level_str(max_level_index, ID_pointer_compound));
}

unsigned pointed_level(const exprt &expr)
{
  if(is_pointed(expr))
    return expr.get_size_t(ID_pointed_level);
  else
    return 0;
}

const irep_idt pointer_level_field(const exprt &expr, const unsigned level)
{
  assert(expr.get(level_str(level, ID_pointer_id))==ID_member);
  return expr.get(level_str(level, ID_pointer_field));
}

const exprt get_pointer(const exprt &expr, unsigned level)
{
  exprt pointer;

  const typet &pointed_type=
    struct_tag_typet(expr.get(level_str(level, ID_pointer_subtype)));

  if(expr.get(level_str(level, ID_pointer_id))==ID_symbol)
  {
    pointer=symbol_exprt(
      expr.get(level_str(level, ID_pointer_sym)),
      pointer_type(pointed_type));
    copy_pointed_info(pointer, expr, level-1);
  }
  else
  {
    assert(expr.get(level_str(level, ID_pointer_id))==ID_member);
    symbol_exprt compound(
      expr.get(level_str(level, ID_pointer_compound)),
      expr.type());
    copy_pointed_info(compound, expr, level-1);
    pointer=member_exprt(
      compound,
      pointer_level_field(expr, level),
      pointer_type(pointed_type));
  }
  return pointer;
}

bool is_pointed(const exprt &expr)
{
  return expr.get_bool(ID_pointed);
}

void copy_pointed_info(exprt &dest, const exprt &src)
{
  copy_pointed_info(dest, src, pointed_level(src)-1);
}

const exprt symbolic_dereference(const exprt &expr, const namespacet &ns)
{
  if(expr.id()==ID_dereference)
  {
    const exprt &pointer=symbolic_dereference(
      to_dereference_expr(expr).pointer(), ns);
    const ssa_objectt pointer_object(pointer, ns);
    if(!pointer_object)
      return expr;

    symbol_exprt sym_deref=pointed_object(pointer_object.symbol_expr(), ns);
    sym_deref.set("#has_symbolic_deref", true);
    return sym_deref;
  }
  else if(expr.id()==ID_member)
  {
    member_exprt member=to_member_expr(expr);
    member.compound()=symbolic_dereference(member.compound(), ns);
    copy_pointed_info(member, member.compound());

    member.set(
      "#has_symbolic_deref",
      has_symbolic_deref(member.compound()));

    return member;
  }
  else
  {
    exprt tmp=expr;
    Forall_operands(it, tmp)
    {
      *it=symbolic_dereference(*it, ns);
      if(has_symbolic_deref(*it))
        tmp.set("#has_symbolic_deref", true);
    }
    return tmp;
  }
}

const std::vector<irep_idt> pointer_fields(
  const exprt &expr,
  const unsigned from_level)
{
  std::vector<irep_idt> result;
  unsigned max_level=pointed_level(expr);
  assert(from_level<max_level);
  for(unsigned l=from_level; l<max_level; ++l)
  {
    result.push_back(pointer_level_field(expr, l));
  }
  return result;
}

const exprt get_pointer_root(const exprt &expr, unsigned level)
{
  exprt pointer=get_pointer(expr, level);
  if(pointer.id()==ID_member)
    pointer=to_member_expr(pointer).compound();
  assert(pointer.id()==ID_symbol);
  return pointer;
}

const irep_idt get_pointer_id(const exprt &expr)
{
  exprt pointer=get_pointer(expr, pointed_level(expr)-1);
  if(pointer.id()==ID_symbol)
    return to_symbol_expr(pointer).get_identifier();
  else if(pointer.id()==ID_member)
  {
    const member_exprt &member=to_member_expr(pointer);
    if(member.compound().id()==ID_symbol)
    {
      return id2string(to_symbol_expr(member.compound()).get_identifier())+
             "."+
             id2string(member.get_component_name());
    }
  }
  return irep_idt();
}

bool has_symbolic_deref(const exprt &expr)
{
  return expr.get_bool("#has_symbolic_deref");
}
