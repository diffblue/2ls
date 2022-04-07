/*******************************************************************\

Module: SSA for malloc()

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// SSA for malloc()

#include <util/std_types.h>
#include <util/std_expr.h>
#include <util/arith_tools.h>
#include <util/expr_util.h>
#include <util/pointer_expr.h>
#include <util/symbol.h>
#include <util/pointer_offset_size.h>
#include <util/c_types.h>

#include <analyses/constant_propagator.h>

#include <functional>

#include "malloc_ssa.h"

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

/// Create new dynamic object, insert it into the symbol table and return its
/// address.
exprt create_dynamic_object(
  const std::string &suffix,
  const typet &type,
  symbol_tablet &symbol_table,
  bool is_concrete)
{
  symbolt value_symbol;

  value_symbol.base_name="dynamic_object"+suffix;
  value_symbol.name="ssa::"+id2string(value_symbol.base_name);
  value_symbol.is_lvalue=true;
  value_symbol.type=type;
  value_symbol.type.set("#dynamic", true);
  value_symbol.mode=ID_C;
  symbol_table.add(value_symbol);

  typet object_type;
  exprt object;

  if(type.id()==ID_array)
  {
    object_type=value_symbol.type.subtype();
    index_exprt index_expr(
      value_symbol.symbol_expr(),
      from_integer(0, index_type()),
      value_symbol.type.subtype());
    object=index_expr;
    if(is_concrete)
      to_index_expr(object).array().set("#concrete", true);
  }
  else
  {
    object=value_symbol.symbol_expr();
    if(is_concrete)
      object.set("#concrete", true);
    object_type=value_symbol.type;
  }

  return address_of_exprt(object, pointer_type(object_type));
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

exprt malloc_ssa(
  const side_effect_exprt &code,
  const std::string &suffix,
  symbol_tablet &symbol_table,
  goto_programt &goto_program,
  goto_programt::targett &i_it,
  bool is_concrete,
  bool alloc_concrete)
{
  if(code.operands().size()!=2)
    throw "allocation expected to have two operands";

  namespacet ns(symbol_table);
  const exprt &size=to_binary_expr(code).op0();
  optionalt<typet> object_type;

  {
    // special treatment for sizeof(T)*x
    if(size.id()==ID_mult &&
       size.operands().size()==2 &&
       to_mult_expr(size).op0().find(ID_C_c_sizeof_type).is_not_nil())
    {
      const mult_exprt &multiplication=to_mult_expr(size);
      if(auto maybe_type=c_sizeof_type_rec(multiplication.op0()))
        object_type=array_typet(
          *maybe_type,
          multiplication.op1());
    }
    else if(size.id()==ID_mult &&
            size.operands().size()==2 &&
            to_mult_expr(size).op1().find(ID_C_c_sizeof_type).is_not_nil())
    {
      const mult_exprt &multiplication=to_mult_expr(size);
      if(auto maybe_type=c_sizeof_type_rec(multiplication.op1()))
        object_type=array_typet(
          *maybe_type,
          multiplication.op0());
    }
    else
    {
      auto maybe_type=c_sizeof_type_rec(size);

      if(maybe_type)
      {
        // Did the size get multiplied?
        if(auto maybe_elem_size=pointer_offset_size(*maybe_type, ns))
        {
          mp_integer alloc_size;
          mp_integer elem_size=*maybe_elem_size;
          if(elem_size<0 || (size.is_constant() &&
            to_integer(to_constant_expr(size), alloc_size)))
          {
          }
          else
          {
            if(alloc_size==elem_size)
              object_type=*maybe_type;
            else
            {
              mp_integer elements=alloc_size/elem_size;

              if(elements*elem_size==alloc_size)
                object_type=array_typet(
                  *maybe_type,
                  from_integer(elements, size.type()));
            }
          }
        }
      }
    }

    // the fall-back is to produce a byte-array
    if(!object_type)
      object_type=array_typet(unsigned_char_type(), size);
  }

#ifdef DEBUG
  std::cout << "OBJECT_TYPE: " << from_type(ns, "", object_type) << std::endl;
#endif

  auto pointers=collect_pointer_vars(symbol_table, *object_type);

  exprt object=create_dynamic_object(
    suffix, *object_type, symbol_table, is_concrete);
  if(object.type()!=code.type())
    object=typecast_exprt(object, code.type());
  exprt result;
  if(!is_concrete && alloc_concrete)
  {
    exprt concrete_object=create_dynamic_object(
      suffix+"$co", *object_type, symbol_table, true);

    // Create nondet symbol
    symbolt nondet_symbol;
    nondet_symbol.base_name="nondet"+suffix;
    nondet_symbol.name="ssa::"+id2string(nondet_symbol.base_name);
    nondet_symbol.is_lvalue=true;
    nondet_symbol.type=bool_typet();
    nondet_symbol.mode=ID_C;
    symbol_table.add(nondet_symbol);

    const exprt nondet_bool_expr =
      side_effect_expr_nondett(bool_typet(), i_it->source_location);
    goto_program.insert_before(
      i_it,
      goto_programt::make_assignment(
        code_assignt(nondet_symbol.symbol_expr(), nondet_bool_expr),
        i_it->source_location));

    exprt::operandst pointer_equs;
    for(auto &ptr : pointers)
    {
      pointer_equs.push_back(equal_exprt(ptr, concrete_object));
    }
    exprt cond=and_exprt(
      nondet_symbol.symbol_expr(),
      not_exprt(disjunction(pointer_equs)));

    if(concrete_object.type()!=code.type())
      concrete_object=typecast_exprt(concrete_object, code.type());
    result=if_exprt(cond, concrete_object, object);
  }
  else
    result=object;

  result.set("#malloc_result", true);

  return result;
}


static bool replace_malloc_rec(
  exprt &expr,
  const std::string &suffix,
  symbol_tablet &symbol_table,
  goto_programt &goto_program,
  goto_programt::targett &i_it,
  const exprt &malloc_size,
  bool is_concrete,
  bool alloc_concrete)
{
  if(expr.id()==ID_side_effect &&
     to_side_effect_expr(expr).get_statement()==ID_allocate)
  {
    assert(!malloc_size.is_nil());
    expr.operands()[0]=malloc_size;

    expr=malloc_ssa(
      to_side_effect_expr(expr),
      "$"+std::to_string(i_it->location_number)+suffix,
      symbol_table,
      goto_program,
      i_it,
      is_concrete,
      alloc_concrete);

    return true;
  }
  else
  {
    bool result=false;
    Forall_operands(it, expr)
    {
      if(replace_malloc_rec(*it,
                            suffix,
                            symbol_table,
                            goto_program,
                            i_it,
                            malloc_size,
                            is_concrete,
                            alloc_concrete))
      {
        result=true;
      }
    }
    return result;
  }
}

/// Finds the latest assignment to lhs before location_number and:
///  - if the assignment rhs is a symbol, continues recursively
///  - otherwise returns the rhs
exprt get_malloc_size(
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
    return get_malloc_size(result, result_loc_num, goto_function);

  return result;
}

bool replace_malloc(
  goto_modelt &goto_model,
  const std::string &suffix,
  bool alloc_concrete)
{
  bool result=false;
  for(auto &f_it : goto_model.goto_functions.function_map)
  {
    goto_programt::const_targett loop_end=f_it.second.body.instructions.end();
    exprt malloc_size=nil_exprt();
    Forall_goto_program_instructions(i_it, f_it.second.body)
    {
      if(loop_end==f_it.second.body.instructions.end())
      {
        for(const auto &incoming : i_it->incoming_edges)
        {
          if(incoming->is_backwards_goto() &&
             incoming!=i_it)
          {
            loop_end=incoming;
          }
        }
      }
      else if(i_it==loop_end)
      {
        loop_end=f_it.second.body.instructions.end();
      }

      if(i_it->is_assign())
      {
        code_assignt &code_assign=to_code_assign(i_it->code_nonconst());
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
            namespacet ns(goto_model.symbol_table);
            goto_functionst::goto_functiont function_copy;
            function_copy.copy_from(f_it.second);
            constant_propagator_ait const_propagator(function_copy);
            const_propagator(f_it.first, function_copy, ns);
            malloc_size=get_malloc_size(
              i_it->assign_lhs(), i_it->location_number, function_copy);
          }
        }
        if(replace_malloc_rec(code_assign.rhs(),
                              suffix,
                              goto_model.symbol_table,
                              f_it.second.body,
                              i_it,
                              malloc_size,
                              loop_end==f_it.second.body.instructions.end(),
                              alloc_concrete))
        {
          result=result || (loop_end!=f_it.second.body.instructions.end());
        }
      }
    }
  }
  goto_model.goto_functions.update();
  return result;
}

/// Replaces the RHS of the following instruction if it is an assignemnt
/// and its LHS is equal to name. Returns whether something was changed.
bool set_following_assign_to_true(
  std::list<goto_programt::instructiont>::iterator it,
  std::list<goto_programt::instructiont>::iterator end,
  const std::string &name)
{
  bool result=false;
  for(; it!=end; it++)
  {
    if(it->is_assign())
    {
      code_assignt &code_assign=to_code_assign(it->code_nonconst());
      if(code_assign.lhs().id()==ID_symbol)
      {
        std::string lhs_id=
          id2string(to_symbol_expr(code_assign.lhs()).get_identifier());
        if(lhs_id==name)
        {
          code_assign.rhs()=true_exprt();
          result=true;
        }
      }
    }
    if(it->is_dead())
    {
      // Stop if the variable is invalid
      const code_deadt &code_dead=code_deadt{it->dead_symbol()};
      if(code_dead.symbol().id()==ID_symbol)
      {
        std::string dead_id=
          id2string(to_symbol_expr(code_dead.symbol()).get_identifier());
        if(name==dead_id)
          break;
      }
    }
    if(it->is_goto())
    {
      // Break on branching, we may not be able to set the variable in all
      // reachable branches, don't even try.
      break;
    }
  }
  return result;
}

/// Set undefined boolean variable to true. Finds declaration of a variable
/// whose name matches the given condition and adds an instruction var = TRUE
/// after the declaration.
/// \par parameters: goto_model
/// name_cond Function returning true for names of variables to be set.
void set_var_always_to_true(
  goto_modelt &goto_model,
  std::function<bool(std::string &)>name_cond)
{
  for(auto &f_it : goto_model.goto_functions.function_map)
  {
    Forall_goto_program_instructions(i_it, f_it.second.body)
    {
      if(i_it->is_decl())
      {
        const code_declt &code_decl=code_declt{i_it->decl_symbol()};
        if(code_decl.symbol().id()==ID_symbol)
        {
          std::string decl_id=
            id2string(to_symbol_expr(code_decl.symbol()).get_identifier());
          if(name_cond(decl_id))
          {
            if(set_following_assign_to_true(
              i_it,
              f_it.second.body.instructions.end(),
              decl_id))
              continue;
            // No following assignment, add one
            f_it.second.body.insert_after(
              i_it,
              goto_programt::make_assignment(
                code_assignt(code_decl.symbol(),true_exprt()),
                i_it->source_location));
          }
        }
      }
    }
    f_it.second.body.compute_location_numbers();
    f_it.second.body.compute_target_numbers();
    f_it.second.body.compute_incoming_edges();
  }
}

void allow_record_malloc(goto_modelt &goto_model)
{
  set_var_always_to_true(
    goto_model,
    [](std::string &name)
    {
      return name.find("malloc::")!=std::string::npos &&
             name.find("::record_malloc")!=std::string::npos;
    });
}

void allow_record_memleak(goto_modelt &goto_model)
{
  set_var_always_to_true(
    goto_model,
    [](std::string &name)
    {
      return name.find("malloc::")!=std::string::npos &&
             name.find("::record_may_leak")!=std::string::npos;
    });
}
