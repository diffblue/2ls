/*******************************************************************\

Module: A flow-insensitive value set analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// A flow-insensitive value set analysis

// #define DEBUG

#ifdef DEBUG
#include <iostream>
#endif

#include <algorithm>

#include <util/pointer_offset_size.h>
#include <util/pointer_expr.h>
#include <util/arith_tools.h>

#include "ssa_value_set.h"
#include "ssa_dereference.h"
#include "ssa_pointed_objects.h"

void ssa_value_domaint::transform(
  const irep_idt &function_from,
  trace_ptrt trace_from,
  const irep_idt &function_to,
  trace_ptrt trace_to,
  ai_baset &ai,
  const namespacet &ns)
{
  locationt from{trace_from->current_location()};
  locationt to{trace_to->current_location()};

  if(has_values.is_false())
    return;
  competition_mode=static_cast<ssa_value_ait &>(ai).options
    .get_bool_option("competition-mode");
  if(from->is_assign())
  {
    exprt lhs_deref=dereference(
      from->assign_lhs(), *this, "", ns, competition_mode);
    exprt rhs_deref=dereference(
      from->assign_rhs(), *this, "", ns, competition_mode);
    assign_lhs_rec(lhs_deref, rhs_deref, ns);
  }
  else if(from->is_goto())
  {
    // Perhaps look at condition, for stuff like
    // p!=0 or the like.
    // exprt cond_deref=dereference(from->guard, *this, "", ns);
  }
  else if(from->is_decl())
  {
    const code_declt &code_decl=code_declt{from->decl_symbol()};
    assign_lhs_rec(code_decl.symbol(), nil_exprt(), ns);
  }
  else if(from->is_function_call())
  {
    const irep_idt &fname=to_symbol_expr(
      from->call_function()).get_identifier();

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

    std::list<symbol_exprt> objects;

    for(auto &argument : from->call_arguments())
    {
      exprt arg=argument;
      exprt arg_expr=argument;
      while(arg.type().id()==ID_pointer)
      {
        if(arg.id()==ID_symbol)
        {
          symbol_exprt pointed_obj=pointed_object(arg, ns);
          pointed_obj.type().set("#dynamic", true);
          objects.push_back(pointed_obj);

          arg_expr=dereference_exprt(arg_expr, arg.type().subtype());
          arg=pointed_obj;
        }
        else if(arg.id()==ID_address_of)
        {
          arg=arg_expr=to_address_of_expr(arg).object();
        }
        else if(arg.id()==ID_typecast)
        {
          assert(arg_expr.id()==ID_typecast);
          arg=arg_expr=to_typecast_expr(arg).op();
        }
        else
          break;
      }
    }

    // the call might come with an assignment
    if(from->call_lhs().is_not_nil())
    {
      exprt lhs_deref=dereference(
        from->call_lhs(), *this, "", ns, competition_mode);
      assign_lhs_rec(lhs_deref, nil_exprt(), ns);
    }

    // the assignment of return value might be in next instruction
    if(to->is_assign() && to->assign_rhs().id()==ID_symbol)
    {
      const symbol_exprt &return_value=to_symbol_expr(to->assign_rhs());
      if(return_value.type().id()==ID_pointer &&
         return_value.get_identifier()==id2string(fname)+"#return_value")
      {
        symbol_exprt pointed_obj=pointed_object(return_value, ns);
        pointed_obj.type().set("#dynamic", true);
        objects.push_back(pointed_obj);
      }
    }

    for(const symbol_exprt &o1 : objects)
    {
      for(const symbol_exprt &o2 : objects)
      {
        if(o1!=o2 && o1.type()==o2.type())
          value_map[ssa_objectt(o1, ns)].value_set.insert(ssa_objectt(o2, ns));
      }
    }
  }
  else if(from->is_dead())
  {
    assign_lhs_rec(from->dead_symbol(), nil_exprt(), ns);
  }
}

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

      auto rhs_it=
        rhs.id()==ID_struct ? rhs.operands().begin() : rhs.operands().end();

      for(struct_typet::componentst::const_iterator
            it=components.begin();
          it!=components.end();
          it++)
      {
        member_exprt new_lhs(lhs, it->get_name(), it->type());
        exprt new_rhs;
        if(rhs_it!=rhs.operands().end())
          new_rhs=*(rhs_it++);
        else
          new_rhs=member_exprt(rhs, it->get_name(), it->type());
        assign_lhs_rec(new_lhs, new_rhs, ns, add); // recursive call
      }

      return; // done
    }

    // object?
    ssa_objectt ssa_object(lhs, ns);

    if(ssa_object)
    {
      // TODO: this is required for interprocedural analysis,
      //       but interferes with intraprocedural analysis
#if 0
      assign_pointed_rhs_rec(rhs, ns);
#endif

      valuest tmp_values;
      assign_rhs_rec(tmp_values, rhs, ns, false, 0);

      valuest &lhs_values=value_map[ssa_object];

      if(add)
        lhs_values.merge(tmp_values);
      else
        lhs_values=tmp_values;

#if 0
      std::cout << "value_set: ";
      lhs_values.output(std::cout, ns);
      std::cout << std::endl;
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
    // not yet removed
    // if there is an array inside a struct referenced by pointer
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
    bool pointer=false;
    bool arithmetics=false;

    forall_operands(it, rhs)
    {
      if(it->type().id()==ID_pointer)
      {
        if(auto maybe_pointer_offset=pointer_offset_size(
          it->type().subtype(),
          ns))
        {
          mp_integer pointer_offset=*maybe_pointer_offset;
          if(pointer_offset<1)
            pointer_offset=1;
          unsigned a=merge_alignment(
            numeric_cast_v<unsigned>(pointer_offset),
            alignment);
          assign_rhs_rec(dest, *it, ns, true, a);

          pointer=true;
        }
      }
      else if(it->type().id()==ID_unsignedbv || it->type().id()==ID_signedbv)
      {
        arithmetics=true;
      }
    }

    if(competition_mode)
      assert(!(pointer && arithmetics));
  }
  else if(rhs.id()==ID_minus)
  {
    assert(rhs.operands().size()==2);
    minus_exprt minus_expr=to_minus_expr(rhs);
    if(rhs.type().id()==ID_pointer)
    {
      if(auto maybe_pointer_offset=
        pointer_offset_size(rhs.type().subtype(), ns))
      {
        mp_integer pointer_offset=*maybe_pointer_offset;
        if(pointer_offset<1)
          pointer_offset=1;
        unsigned a=merge_alignment(
          numeric_cast_v<unsigned>(pointer_offset),
          alignment);
        assign_rhs_rec(dest, minus_expr.op0(), ns, true, a);

        if(competition_mode)
          assert(
            !(minus_expr.op1().type().id()==ID_unsignedbv ||
              minus_expr.op1().type().id()==ID_signedbv));
      }
    }
  }
  else if(rhs.id()==ID_dereference)
  {
    // not yet removed
    // if there is an array inside a struct referenced by pointer
    assign_rhs_rec(dest, to_dereference_expr(rhs).op(), ns, true, 1);
  }
  else
  {
    // object?

    ssa_objectt ssa_object(rhs, ns);

    if(ssa_object)
    {
      value_mapt::const_iterator m_it=value_map.find(ssa_object);

      if(m_it!=value_map.end())
      {
        valuest tmp_values=m_it->second;
        if(offset)
          tmp_values.offset=true;
        tmp_values.alignment=merge_alignment(tmp_values.alignment, alignment);
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
    dest.value_set.insert(ssa_object);
    if(offset)
      dest.offset=true;
  }
  else if(rhs.id()==ID_if)
  {
    assign_rhs_rec_address_of(
      dest, to_if_expr(rhs).true_case(), ns, offset, alignment);
    assign_rhs_rec_address_of(
      dest, to_if_expr(rhs).false_case(), ns, offset, alignment);
  }
  else if(rhs.id()==ID_index)
  {
    unsigned a=alignment;

    if(!to_index_expr(rhs).index().is_zero())
    {
      offset=true;
      if(auto maybe_pointer_offset=pointer_offset_size(rhs.type(), ns))
      {
        mp_integer pointer_offset=*maybe_pointer_offset;
        if(pointer_offset<1)
          pointer_offset=1;
        a=merge_alignment(
          a,
          numeric_cast_v<unsigned>(pointer_offset));
      }
    }

    assign_rhs_rec_address_of(dest, to_index_expr(rhs).array(), ns, offset, a);
  }
}

void ssa_value_domaint::valuest::output(
  std::ostream &out,
  const namespacet &ns) const
{
  if(offset)
  {
    out << " offset";
    if(alignment!=0)
      out << "*" << alignment;
  }

  if(null)
    out << " null";
  if(unknown)
    out << " unknown";
  if(integer_address)
    out << " integer_address";

  for(value_sett::const_iterator it=value_set.begin();
      it!=value_set.end();
      it++)
    out << ' ' << '&' << it->get_identifier();
}

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

/// \return Return true if "this" has changed.
bool ssa_value_domaint::valuest::merge(
  const valuest &src,
  bool is_loop_back,
  const irep_idt &object_id)
{
  bool result=false;

  // bits
  if(src.offset && !offset)
  {
    offset=true;
    result=true;
  }
  if(src.null && !null)
  {
    null=true;
    result=true;
  }
  if(src.unknown && !unknown)
  {
    unknown=true;
    result=true;
  }
  if(src.integer_address && !integer_address)
  {
    integer_address=true;
    result=true;
  }

  // value set
  unsigned long old_size=value_set.size();
  for(const ssa_objectt &v : src.value_set)
  {
    if(is_loop_back)
    {
      if(is_pointed(v.get_expr()))
      {
        unsigned level=pointed_level(v.get_expr())-1;
        exprt expr=v.get_expr();

        auto it=value_set.end();

        while(level>0)
        {
          const irep_idt ptr_root_id=pointer_root_id(expr);
          it=std::find_if(
            value_set.begin(),
            value_set.end(),
            [&ptr_root_id](const ssa_objectt &o)
            { return o.get_identifier()==ptr_root_id; });
          if(it!=value_set.end())
            break;
          else
          {
            expr=get_pointer_root(expr, level--);
          }
        }

        if(it!=value_set.end())
          continue;
      }
    }
    value_set.insert(v);
  }
  if(value_set.size()!=old_size)
    result=true;

  // alignment
  alignment=merge_alignment(alignment, src.alignment);

  return result;
}

/// \return Return true if "this" has changed.
bool ssa_value_domaint::merge(
  const ssa_value_domaint &other,
  trace_ptrt trace_from,
  trace_ptrt trace_to)
{
  locationt from{trace_from->current_location()};

  value_mapt::iterator v_it=value_map.begin();
  const value_mapt &new_value_map=other.value_map;
  bool result=has_values.is_false() && !other.has_values.is_false();
  has_values=tvt::unknown();

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

    if(v_it->second.merge(it->second, from->is_backwards_goto(),
                          it->first.get_identifier()))
      result=true;

    v_it++;
    it++;
  }

  competition_mode=competition_mode || other.competition_mode;

  return result;
}

/// Dynamically add p'obj to value set of p
void ssa_value_domaint::assign_pointed_rhs_rec(
  const exprt &rhs,
  const namespacet &ns)
{
  ssa_objectt ssa_object(rhs, ns);

  if(ssa_object && ssa_object.type().id()==ID_pointer)
  {
    if(ssa_object.get_root_object().get_bool("#unknown_obj"))
      return;

    value_mapt::const_iterator m_it=value_map.find(ssa_object);

    if(m_it==value_map.end())
    {
      const symbol_exprt pointed=pointed_object(rhs, ns);
      ssa_objectt pointed_obj(pointed, ns);
      value_map[ssa_object].value_set.insert(pointed_obj);
    }
  }
  else
  {
    forall_operands(it, rhs)
      assign_pointed_rhs_rec(*it, ns);
  }
}

/// Initialize value sets for pointer parameters and pointer-typed fields of
/// objects pointed by parameters.
/// \par parameters: GOTO function
void ssa_value_ait::initialize(
  const irep_idt &function_id,
  const goto_functionst::goto_functiont &goto_function)
{
  ait<ssa_value_domaint>::initialize(function_id, goto_function);
  forall_goto_program_instructions(i_it, goto_function.body)
    get_state(i_it).make_bottom();

  // Initialize value sets for pointer parameters

  auto function_symbol=ns.lookup(function_id);
  const code_typet::parameterst params=
    to_code_type(function_symbol.type).parameters();
  if(!params.empty())
  {
    auto entry_s=entry_state(goto_function.body);
    ssa_value_domaint &entry=dynamic_cast<ssa_value_domaint &>(
      get_state(entry_s));

    for(auto &param : params)
    {
      const symbol_exprt param_expr(param.get_identifier(), param.type());
      assign_ptr_param(param_expr, entry);
    }
  }
}

/// Initialize value set for the given expression and recursively for all
/// structure members and all pointed objects. Pointer-typed variable p
/// initially points to abstract object p'obj. Pointer-typed field of structure
/// initially points to advancer.
/// \par parameters: Expression to be initialized and entry record of value set
///   analysis
void ssa_value_ait::assign_ptr_param(
  const exprt &expr,
  ssa_value_domaint &entry)
{
  const typet &type=ns.follow(expr.type());
  if(type.id()==ID_pointer)
  {
    if(expr.id()==ID_symbol)
    {
      // pointer variable
      symbol_exprt pointed_expr=pointed_object(expr, ns);
      assign(expr, pointed_expr, entry);
      assign_ptr_param(pointed_expr, entry);
    }
  }
  else if(type.id()==ID_struct)
  {
    // split structure into fields
    for(auto &component : to_struct_type(type).components())
    {
      const member_exprt member(expr, component.get_name(), component.type());
      assign_ptr_param(member, entry);
    }
  }
}

/// Insert object to value set of another object in the given entry.
/// \par parameters: Pointer variable src, pointed object dest and analysis
///   entry.
void ssa_value_ait::assign(
  const exprt &src,
  const exprt &dest,
  ssa_value_domaint &entry)
{
  ssa_objectt src_obj(src, ns);
  ssa_objectt dest_obj(dest, ns);
  if(src_obj && dest_obj)
  {
    entry.value_map[src_obj].value_set.insert(dest_obj);
  }
}
