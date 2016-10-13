/*******************************************************************\

Module: SSA Objects

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

//#define DEBUG

#ifdef DEBUG
#include <iostream>
#include <langapi/language_util.h>
#endif

#include <util/expr_util.h>

#include <analyses/dirty.h>

#include "ssa_object.h"

/*******************************************************************\

Function: is_ptr_object

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool is_ptr_object(const exprt &src)
{
  return src.id()==ID_symbol &&
         src.get(ID_ptr_object)!=irep_idt();
}

/*******************************************************************\

Function: collect_objects_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void collect_objects_rec(
  const exprt &src,
  const namespacet &ns,
  std::set<ssa_objectt> &objects,
  std::set<exprt> &literals);

void collect_ptr_objects(const exprt &expr,
                         const namespacet &ns,
                         std::set<ssa_objectt> &objects,
                         std::set<exprt> &literals)
{
  if (expr.id() == ID_symbol)
  {
    const symbol_exprt &src = to_symbol_expr(expr);
    const typet &type = ns.follow(src.type());
    if (type.id() == ID_pointer)
    {
      const irep_idt &identifier = id2string(src.get_identifier()) + "'obj";
      const typet &pointed_type = src.type().subtype();
      symbol_exprt ptr_object(identifier, pointed_type);

      if (is_ptr_object(src))
        ptr_object.set(ID_ptr_object, src.get(ID_ptr_object));
      else
        ptr_object.set(ID_ptr_object, src.get_identifier());

      collect_objects_rec(ptr_object, ns, objects, literals);
      collect_ptr_objects(ptr_object, ns, objects, literals);
    }
  }
  else
  {
    forall_operands(it, expr)
      collect_ptr_objects(*it, ns, objects, literals);
  }
}

void collect_objects_address_of_rec(
  const exprt &src,
  const namespacet &ns,
  std::set<ssa_objectt> &objects,
  std::set<exprt> &literals)
{
#ifdef DEBUG
  std::cout << "COLLECT ADDRESS OF " << from_expr(ns,"",src) << "\n";
#endif
  
  if(src.id()==ID_index)
  {
    collect_objects_address_of_rec(
      to_index_expr(src).array(), ns, objects, literals);

    collect_objects_rec(
      to_index_expr(src).index(), ns, objects, literals);
  }
  else if(src.id()==ID_dereference)
  {
    collect_objects_rec(
      to_dereference_expr(src).pointer(), ns, objects, literals);
  }
  else if(src.id()==ID_member)
  {
    collect_objects_address_of_rec(
      to_member_expr(src).struct_op(), ns, objects, literals);
  }
  else if(src.id()==ID_string_constant)
  {
    literals.insert(src);
  }
  else if(src.id()==ID_symbol)
  {
    collect_objects_rec(
      src, ns, objects, literals);
  }
}

/*******************************************************************\

Function: collect_objects_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void collect_objects_rec(
  const exprt &src,
  const namespacet &ns,
  std::set<ssa_objectt> &objects,
  std::set<exprt> &literals)
{

 #ifdef DEBUG
  std::cout << "COLLECT " << from_expr(ns,"",src) << "\n";
 #endif

  if(src.id()==ID_code)
  {
    forall_operands(it, src)
      collect_objects_rec(*it, ns, objects, literals);

    const codet &code = to_code(src);
    if (code.get_statement() == ID_function_call)
    {
      const code_function_callt &function_call = to_code_function_call(code);
      for (auto &arg : function_call.arguments())
        collect_ptr_objects(arg, ns, objects, literals);
    }

    return;
  }
  else if(src.id()==ID_address_of)
  {
    collect_objects_address_of_rec(
      to_address_of_expr(src).object(), ns, objects, literals);
    return;
  }

  const typet &type=ns.follow(src.type());

  // don't collect function-typed objects
  if(src.id()==ID_symbol && type.id()==ID_code)
    return;

  ssa_objectt ssa_object(src, ns);

  if(ssa_object)
  {
    if(type.id()==ID_struct)
    {
      std::string id = id2string(ssa_object.get_identifier());
      if (src.type().get_bool("#dynamic") || id.find("'obj") == id.size() - 4)
        objects.insert(ssa_object);

      // need to split up

      const struct_typet &struct_type=to_struct_type(type);
      const struct_typet::componentst &components=struct_type.components();
      
      for(struct_typet::componentst::const_iterator
          it=components.begin();
          it!=components.end();
          it++)
      {
        member_exprt new_src(src, it->get_name(), it->type());
        collect_objects_rec(new_src, ns, objects, literals); // recursive call
      }
    }
    else
    {

 #ifdef DEBUG
      std::cout << "OBJECT " << ssa_object.get_identifier() << "\n";
 #endif

      objects.insert(ssa_object);

      const exprt &root_object = ssa_object.get_root_object();
      const symbolt *symbol;
      if (ssa_object.type().get_bool("#dynamic") ||
          (root_object.id() == ID_symbol &&
           !ns.lookup(to_symbol_expr(root_object).get_identifier(), symbol) &&
           (symbol->is_parameter || !symbol->is_procedure_local())))
        collect_ptr_objects(ssa_object.symbol_expr(), ns, objects, literals);
    }
  }
  else
  {
    forall_operands(it, src)
      collect_objects_rec(*it, ns, objects, literals);
  }
}

/*******************************************************************\

Function: ssa_objectst::collect_objects

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_objectst::collect_objects(
  const goto_functionst::goto_functiont &src,
  const namespacet &ns)
{
  // Add objects for parameters.
  for(goto_functionst::goto_functiont::parameter_identifierst::
      const_iterator it=src.parameter_identifiers.begin();
      it!=src.parameter_identifiers.end();
      it++)
  {
    symbol_exprt symbol=ns.lookup(*it).symbol_expr();
    collect_objects_rec(symbol, ns, objects, literals);
    collect_ptr_objects(symbol, ns, objects, literals);
  }

  // Rummage through body.
  forall_goto_program_instructions(it, src.body)
  {
    collect_objects_rec(it->guard, ns, objects, literals);
    collect_objects_rec(it->code, ns, objects, literals);
  }
}

/*******************************************************************\

Function: ssa_objectst::add_ptr_objects

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_objectst::add_ptr_objects(const goto_functionst::goto_functiont &goto_function,
                                   const namespacet &ns)
{
  objectst tmp;

  for(objectst::const_iterator o_it=objects.begin();
      o_it!=objects.end();
      o_it++)
  {
    exprt root_object=o_it->get_root_object();
    if(root_object.id()==ID_symbol)
    {
      const symbolt &symbol = ns.lookup(root_object);
      dirtyt dirty(goto_function);
      if(o_it->type().id()==ID_pointer &&
          (symbol.is_parameter || !symbol.is_procedure_local() || dirty(symbol.name)))
      {
        tmp.insert(*o_it);
      }
    }
  }
  
  for(objectst::const_iterator o_it=tmp.begin();
      o_it!=tmp.end();
      o_it++)
  {
    typet type = o_it->type();
    irep_idt identifier = o_it->get_identifier();
    do
    {
      type = type.subtype();
      identifier = id2string(identifier) + "'obj";
      symbol_exprt ptr_object(identifier, type);
      ptr_object.set(ID_ptr_object, o_it->get_identifier());
      collect_objects_rec(ptr_object, ns, objects, literals);
    } while (ns.follow(type).id() == ID_pointer);
  }
}

/*******************************************************************\

Function: ssa_objectst::categorize_objects

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_objectst::categorize_objects(
  const goto_functionst::goto_functiont &goto_function,
  const namespacet &ns)
{
  dirtyt dirty(goto_function);

  for(objectst::const_iterator o_it=objects.begin();
      o_it!=objects.end();
      o_it++)
  {
    exprt root_object=o_it->get_root_object();

#ifdef DEBUG
    std::cout << "CATEGORIZE " << from_expr(ns,"",root_object) << "\n";
#endif

    if(root_object.id()==ID_symbol)
    {
      if(is_ptr_object(root_object) || root_object.type().get_bool("#dynamic"))
      {
        globals.insert(*o_it);
      }
      else
      {
        const symbolt &symbol=ns.lookup(root_object);
        if(symbol.is_procedure_local())
        {
          if(dirty(symbol.name))
            dirty_locals.insert(*o_it);
          else
            clean_locals.insert(*o_it);
        }
        else
          globals.insert(*o_it);
      }
    }
  }
}

/*******************************************************************\

Function: ssa_objectt::get_root_object_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt ssa_objectt::get_root_object_rec(const exprt &src)
{
  if(src.id()==ID_symbol)
  {
    return src;
  }
  else if(src.id()==ID_member)
  {
    const member_exprt &member_expr=to_member_expr(src);
    return member_expr.struct_op();
  }
  else if(src.id()==ID_index)
  {
    const index_exprt &index_expr=to_index_expr(src);
    return index_expr.array();
  }
  else
    return nil_exprt();
}

/*******************************************************************\

Function: ssa_objectt::object_id_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

ssa_objectt::identifiert ssa_objectt::object_id_rec(
  const exprt &src,
  const namespacet &ns)
{
  if(src.id()==ID_symbol)
  {
    return identifiert(to_symbol_expr(src).get_identifier());
  }
  else if(src.id()==ID_member)
  {
    const member_exprt &member_expr=to_member_expr(src);
    const exprt &compound_op=member_expr.struct_op();
    
    // need to distinguish union and struct members
    if(is_struct_member(member_expr, ns))
    {
      irep_idt compound_object=object_id_rec(compound_op, ns);
      if(compound_object==irep_idt()) return identifiert();
    
      return identifiert(
        id2string(compound_object)+
        "."+id2string(member_expr.get_component_name()));
    }
    else
      return identifiert();
  }
  else if(src.id()==ID_index)
  {
    return identifiert();
  }
  else if(src.id()==ID_dereference)
  {
    return identifiert();
  }
  else
    return identifiert();
}

/*******************************************************************\

Function: is_struct_member

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool is_struct_member(const member_exprt &src, const namespacet &ns)
{
  const exprt &compound_op=src.struct_op();
  const typet &compound_type=ns.follow(compound_op.type());

  return compound_type.id()==ID_struct;
}

/*******************************************************************\

Function: get_struct_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const exprt &get_struct_rec(const exprt &src, const namespacet &ns)
{
  // Returns X for X(.member)*, where
  // all members are struct members.
  if(src.id()==ID_member)
  {
    const member_exprt &member_expr=to_member_expr(src);
    const exprt &compound_op=member_expr.struct_op();

    // need to distinguish union and struct members
    if(is_struct_member(member_expr, ns))
      return get_struct_rec(compound_op, ns);
    else
      return src;
  }
  else
    return src;
}

/*******************************************************************\

Function: is_symbol_struct_member

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

// Returns true for symbol(.member)*, where
// all members are struct members.
bool is_symbol_struct_member(const exprt &src, const namespacet &ns)
{
  return get_struct_rec(src, ns).id()==ID_symbol;
}

/*******************************************************************\

Function: is_symbol_or_deref_struct_member

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

// Returns true for ((*ptr)|symbol)(.member)*, where
// all members are struct members.
bool is_symbol_or_deref_struct_member(const exprt &src, const namespacet &ns)
{
  exprt struct_op=get_struct_rec(src, ns);
  return struct_op.id()==ID_symbol || struct_op.id()==ID_dereference;
}

/*******************************************************************\

Function: is_deref_struct_member

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

// Returns true for (*ptr)(.member)*, where
// all members are struct members.
bool is_deref_struct_member(const exprt &src, const namespacet &ns)
{
  return get_struct_rec(src, ns).id()==ID_dereference;
}

