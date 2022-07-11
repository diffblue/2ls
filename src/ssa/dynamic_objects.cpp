/*******************************************************************\

Module: Dynamically allocated objects

Author: Viktor Malik

\*******************************************************************/

#include "dynamic_objects.h"
#include "dynobj_instance_analysis.h"
#include "ssa_value_set.h"

#include <analyses/constant_propagator.h>
#include <util/c_types.h>
#include <util/expr_util.h>
#include <util/type.h>
#include <util/pointer_offset_size.h>
#include <util/arith_tools.h>

#include <algorithm>
#include <iostream>

dynamic_objectt::dynamic_objectt(
  const goto_programt::instructiont *loc,
  const typet &type,
  const std::string &suffix,
  bool concrete)
  :loc(loc), concrete(concrete)
{
  symbol.base_name=
    "dynamic_object$"+std::to_string(loc->location_number)+suffix;
  symbol.name="ssa::"+id2string(symbol.base_name);
  symbol.is_lvalue=true;
  symbol.type=type;
  symbol.type.set("#dynamic", true);
  symbol.mode=ID_C;
}

exprt dynamic_objectt::address_of(const typet &result_type) const
{
  typet object_type;
  exprt object;

  if(symbol.type.id()==ID_array)
  {
    object_type=symbol.type.subtype();
    index_exprt index_expr(
      symbol.symbol_expr(),
      from_integer(0, index_type()),
      symbol.type.subtype());
    object=index_expr;
    if(concrete)
      to_index_expr(object).array().set("#concrete", true);
  }
  else
  {
    object=symbol.symbol_expr();
    if(concrete)
      object.set("#concrete", true);
    object_type=symbol.type;
  }

  auto result=address_of_exprt(object, pointer_type(object_type));
  if(result.type()!=result_type)
    return typecast_exprt(result, result_type);
  return std::move(result);
}

void dynamic_objectst::replace_malloc(bool with_concrete)
{
  for(auto &f_it : goto_model.goto_functions.function_map)
  {
    for(auto &i_it : f_it.second.body.instructions)
    {
      // Update current loop
      if(!loop_end)
      {
        for(const auto &incoming : i_it.incoming_edges)
        {
          if(incoming->is_backwards_goto() && &*incoming!=&i_it)
            loop_end=&*incoming;
        }
      }
      else if(&i_it==loop_end)
        loop_end=nullptr;

      get_malloc_size(i_it, f_it.second);

      if(i_it.is_assign())
        replace_malloc_rec(
          to_code_assign(i_it.code_nonconst()).rhs(), i_it, with_concrete);
    }
  }
}

/// Finds the latest assignment to lhs before location_number and:
///  - if the assignment rhs is a symbol, continues recursively
///  - otherwise returns the rhs
exprt get_malloc_size_expr(
  const exprt &lhs,
  unsigned location_number,
  const goto_functiont &goto_function)
{
  exprt result=nil_exprt();
  unsigned result_loc_num=0;
  forall_goto_program_instructions(it, goto_function.body)
  {
    if(!it->is_assign())
      continue;

    if(lhs==it->assign_lhs())
    {
      result=it->assign_rhs();
      if(result.id()==ID_typecast)
        result=to_typecast_expr(result).op();
      result_loc_num=it->location_number;
    }

    if(it->location_number==location_number)
      break;
  }
  if(result.id()==ID_symbol)
    return get_malloc_size_expr(result, result_loc_num, goto_function);

  return result;
}

bool dynamic_objectst::get_malloc_size(
  const goto_programt::instructiont &loc,
  const goto_functionst::goto_functiont &current_function)
{
  if(loc.is_assign())
  {
    const code_assignt &code_assign=to_code_assign(loc.get_code());
    if(code_assign.lhs().id()==ID_symbol)
    {
      // we have to propagate the malloc size
      //   in order to get the object type
      // TODO: this only works with inlining,
      //       and btw, this is an ugly hack
      std::string lhs_id=
        id2string(to_symbol_expr(code_assign.lhs()).get_identifier());
      if(lhs_id=="malloc::malloc_size" ||
         lhs_id=="__builtin_alloca::alloca_size")
      {
        goto_functionst::goto_functiont function_copy;
        function_copy.copy_from(current_function);
        constant_propagator_ait const_propagator(function_copy);
        const_propagator("", function_copy, ns);
        malloc_size=get_malloc_size_expr(
          loc.assign_lhs(), loc.location_number, function_copy);
      }
    }
  }
  return false;
}

void dynamic_objectst::replace_malloc_rec(
  exprt &malloc_expr,
  const goto_programt::instructiont &loc,
  bool with_concrete)
{
  if(malloc_expr.id()==ID_side_effect &&
     to_side_effect_expr(malloc_expr).get_statement()==ID_allocate)
  {
    auto object_type=get_object_type();
    auto &dynobj=create_dynamic_object(loc, object_type, "", !loop_end);
    exprt result_expr=dynobj.address_of(malloc_expr.type());

    if(with_concrete && loop_end)
    {
      auto &concrete_dynobj=create_dynamic_object(
        loc, object_type, "$co", true);
      auto concrete_select=get_concrete_object_guard(loc, concrete_dynobj);

      result_expr=if_exprt(
        concrete_select, concrete_dynobj.address_of(malloc_expr.type()),
        result_expr);
    }

    malloc_expr=result_expr;
    malloc_expr.set("#malloc_result", true);
    malloc_size=nil_exprt();
  }
  else
    Forall_operands(it, malloc_expr)
      replace_malloc_rec(*it, loc, with_concrete);
}

inline static optionalt<typet> c_sizeof_type_rec(const exprt &expr)
{
  const irept &sizeof_type=expr.find(ID_C_c_sizeof_type);

  if(!sizeof_type.is_nil())
  {
    return static_cast<const typet &>(sizeof_type);
  }
  else if(expr.id()==ID_mult)
  {
    forall_operands(it, expr)
    {
      if(auto maybe_t=c_sizeof_type_rec(*it))
        return maybe_t;
    }
  }

  return {};
}

typet dynamic_objectst::get_object_type()
{
  assert(!malloc_size.is_nil());

  optionalt<typet> object_type={};

  // special treatment for sizeof(T)*x
  if(malloc_size.id()==ID_mult &&
     malloc_size.operands().size()==2 &&
     (to_mult_expr(malloc_size).op0().find(ID_C_c_sizeof_type).is_not_nil() ||
      to_mult_expr(malloc_size).op1().find(ID_C_c_sizeof_type).is_not_nil()))
  {
    const mult_exprt &multiplication=to_mult_expr(malloc_size);

    optionalt<typet> base_type;
    exprt array_size;

    if(multiplication.op0().find(ID_C_c_sizeof_type).is_not_nil())
    {
      base_type=c_sizeof_type_rec(multiplication.op0());
      array_size=multiplication.op1();
    }
    else
    {
      base_type=c_sizeof_type_rec(multiplication.op1());
      array_size=multiplication.op0();
    }

    if(base_type)
      object_type=array_typet(*base_type, array_size);
  }
  else
  {
    auto maybe_type=c_sizeof_type_rec(malloc_size);

    if(maybe_type)
    {
      // Did the size get multiplied?
      if(auto maybe_elem_size=pointer_offset_size(*maybe_type, ns))
      {
        mp_integer alloc_size;
        mp_integer elem_size=*maybe_elem_size;
        if(elem_size>=0 && (!malloc_size.is_constant() || !to_integer(
          to_constant_expr(malloc_size), alloc_size)))
        {
          if(alloc_size==elem_size)
            object_type=*maybe_type;
          else
          {
            mp_integer elements=alloc_size/elem_size;

            if(elements*elem_size==alloc_size)
              object_type=array_typet(
                *maybe_type,
                from_integer(elements, malloc_size.type()));
          }
        }
      }
    }
  }

  // the fall-back is to produce a byte-array
  if(!object_type)
    object_type=array_typet(unsigned_char_type(), malloc_size);

  return *object_type;
}

dynamic_objectt &dynamic_objectst::create_dynamic_object(
  const goto_programt::instructiont &loc,
  const typet &type,
  const std::string &suffix,
  bool concrete)
{
  db[&loc].push_back(dynamic_objectt(&loc, type, suffix, concrete));
  auto &dynobj=db[&loc].back();
  goto_model.symbol_table.add(dynobj.get_symbol());
  return dynobj;
}

symbol_exprt dynamic_objectst::create_object_select(
  const goto_programt::instructiont &loc,
  const std::string &suffix)
{
  symbolt guard_symbol;
  guard_symbol.base_name=
    "$guard#os"+std::to_string(loc.location_number)+"$"+suffix;
  guard_symbol.name="ssa::"+id2string(guard_symbol.base_name);
  guard_symbol.is_lvalue=true;
  guard_symbol.type=bool_typet();
  guard_symbol.mode=ID_C;
  goto_model.symbol_table.add(guard_symbol);

  return guard_symbol.symbol_expr();
}

/// Collect all variables (symbols and their members) of pointer type with given
/// pointed type.
std::vector<exprt> collect_pointer_vars(
  const symbol_tablet &symbol_table,
  const typet &pointed_type)
{
  namespacet ns(symbol_table);
  std::vector<exprt> pointers;
  for(const auto &it : symbol_table.symbols)
  {
    if(it.second.is_type)
      continue;
    if(ns.follow(it.second.type).id()==ID_struct)
    {
      for(auto &component : to_struct_type(
        ns.follow(it.second.type)).components())
      {
        if(component.type().id()==ID_pointer)
        {
          if(ns.follow(component.type().subtype())==ns.follow(pointed_type))
          {
            pointers.push_back(
              member_exprt(
                it.second.symbol_expr(), component.get_name(),
                component.type()));
          }
        }
      }
    }
    if(it.second.type.id()==ID_pointer)
    {
      if(ns.follow(it.second.type.subtype())==ns.follow(pointed_type))
      {
        pointers.push_back(it.second.symbol_expr());
      }
    }
  }
  return pointers;
}

exprt dynamic_objectst::get_concrete_object_guard(
  const goto_programt::instructiont &loc,
  const dynamic_objectt &concrete_object)
{
  auto select_guard=create_object_select(loc, "co");

  exprt::operandst pointer_equs;
  for(auto &ptr : collect_pointer_vars(
    goto_model.symbol_table, concrete_object.type()))
  {
    pointer_equs.push_back(
      equal_exprt(ptr, concrete_object.address_of(ptr.type())));
  }

  return and_exprt(
    select_guard,
    not_exprt(disjunction(pointer_equs)));
}

void dynamic_objectst::clear(const goto_programt::instructiont &loc)
{
  auto objs=db.find(&loc);
  if(objs!=db.end())
    objs->second.clear();
}

const std::vector<dynamic_objectt> &dynamic_objectst::get_objects(
  const goto_programt::instructiont &loc) const
{
  return db.at(&loc);
}

void dynamic_objectst::generate_instances(const optionst &options)
{
  for(auto &f_it : goto_model.goto_functions.function_map)
  {
    if(!f_it.second.body_available())
      continue;
    ssa_value_ait value_analysis(f_it.first, f_it.second, ns, options);
    dynobj_instance_analysist do_inst(
      f_it.first, f_it.second, ns, options, value_analysis, *this);

    auto instances=compute_instance_numbers(f_it.second.body, do_inst);
    Forall_goto_program_instructions(i_it, f_it.second.body)
    {
      if(!i_it->is_assign())
        continue;
      auto &assign=to_code_assign(i_it->code_nonconst());
      if(!assign.rhs().get_bool("#malloc_result"))
        continue;

      auto *obj=get_single_abstract_object(*i_it);
      if(!obj)
        continue;
      const symbol_exprt obj_symbol=obj->symbol_expr(); // copy

      auto new_objs=split_object(
        obj, instances.at(obj->symbol_expr()), assign.lhs().type());
      new_objs.set("#malloc_result", true);
      replace_object(obj_symbol, new_objs, assign.rhs());
    }
  }
}

dynamic_objectst::instance_countst dynamic_objectst::compute_instance_numbers(
  const goto_programt &goto_program,
  const dynobj_instance_analysist &analysis)
{
  instance_countst instance_counts;
  forall_goto_program_instructions(it, goto_program)
  {
    auto &analysis_value=analysis[it];
    for(auto &obj : analysis_value.live_pointers)
    {
      auto must_alias=analysis_value.must_alias_relations.find(obj.first);
      if(must_alias==analysis_value.must_alias_relations.end())
        continue;

      std::set<size_t> alias_classes;
      for(auto &expr : obj.second)
      {
        size_t n;
        const auto number=must_alias->second.data.get_number(expr);
        if(!number)
          continue;
        n=*number;
        alias_classes.insert(must_alias->second.data.find_number(n));
      }

      if(instance_counts.find(obj.first)==instance_counts.end() ||
         instance_counts.at(obj.first)<alias_classes.size())
      {
        instance_counts[obj.first]=alias_classes.size();
      }
    }
  }
  return instance_counts;
}

const dynamic_objectt *dynamic_objectst::get_single_abstract_object(
  const goto_programt::instructiont &loc)
{
  auto &objs=get_objects(loc);
  if(objs.size()==1 && !objs.front().concrete)
    return &objs.front();
  if(objs.size()==2)
  {
    if(!objs.at(0).concrete)
    {
      assert(objs.at(1).concrete);
      return &objs.at(0);
    }
    if(!objs.at(1).concrete)
    {
      assert(objs.at(0).concrete);
      return &objs.at(1);
    }
  }
  return nullptr;
}

exprt dynamic_objectst::split_object(
  const dynamic_objectt *object,
  unsigned int cnt,
  const typet &result_type)
{
  if(cnt<=1)
    return object->address_of(result_type);

  // Need to copy the object as the pointer will get invalidated upon inserting
  // new objects.
  const dynamic_objectt obj_copy(*object);

  auto &first_instance=create_dynamic_object(
    *obj_copy.loc, obj_copy.type(), "$"+std::to_string(0), false);
  exprt result=first_instance.address_of(result_type);

  for(auto i=1; i<cnt; i++)
  {
    auto &instance=create_dynamic_object(
      *obj_copy.loc,
      obj_copy.type(),
      "$"+std::to_string(i),
      false);
    auto guard=create_object_select(*obj_copy.loc, std::to_string(i));

    result=if_exprt(guard, instance.address_of(result_type), result);
  }

  erase_obj(obj_copy);

  return result;
}

void dynamic_objectst::erase_obj(const dynamic_objectt &obj)
{
  auto &objs=db.at(obj.loc);
  objs.erase(std::remove(objs.begin(), objs.end(), obj), objs.end());
}

void dynamic_objectst::replace_object(
  const symbol_exprt &object,
  const exprt &new_expr,
  exprt &expr)
{
  if(expr.id()==ID_address_of &&
     to_address_of_expr(expr).object()==object)
  {
    expr=new_expr;
  }
  else
    Forall_operands(o_it, expr)
      replace_object(object, new_expr, *o_it);
}

/// \param id: Symbol identifier.
/// \return If the symbol is a dynamic object, then the location number of the
///   malloc call where the object was allocated, otherwise -1.
int get_dynobj_line(const irep_idt &id)
{
  std::string name=id2string(id);
  size_t pos=name.find("dynamic_object$");
  if(pos==std::string::npos)
    return -1;

  size_t start=pos+15;
  size_t end=name.find_first_not_of("0123456789", start);
  std::string number=name.substr(start, end-start);
  return std::stoi(number);
}
