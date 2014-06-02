/*******************************************************************\

Module: SSA Objects

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "ssa_object.h"

/*******************************************************************\

Function: collect_objects_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void collect_objects_rec(
  const exprt &src,
  const namespacet &ns,
  std::set<ssa_objectt> &dest);

void collect_objects_address_of_rec(
  const exprt &src,
  const namespacet &ns,
  std::set<ssa_objectt> &dest)
{
  if(src.id()==ID_index)
  {
    collect_objects_address_of_rec(to_index_expr(src).array(), ns, dest);
    collect_objects_rec(to_index_expr(src).index(), ns, dest);
  }
  else if(src.id()==ID_dereference)
  {
    collect_objects_rec(to_dereference_expr(src).pointer(), ns, dest);
  }
  else if(src.id()==ID_member)
  {
    collect_objects_address_of_rec(to_member_expr(src).struct_op(), ns, dest);
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
  std::set<ssa_objectt> &dest)
{
  if(src.id()==ID_code)
  {
    forall_operands(it, src)
      collect_objects_rec(*it, ns, dest);
    return;
  }
  else if(src.id()==ID_address_of)
  {
    collect_objects_address_of_rec(
      to_address_of_expr(src).object(), ns, dest);
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
      // need to split up

      const struct_typet &struct_type=to_struct_type(type);
      const struct_typet::componentst &components=struct_type.components();
      
      for(struct_typet::componentst::const_iterator
          it=components.begin();
          it!=components.end();
          it++)
      {
        member_exprt new_src(src, it->get_name(), it->type());
        collect_objects_rec(new_src, ns, dest); // recursive call
      }
      
      return; // done
    }
    
    dest.insert(ssa_object);
  }
  else
  {
    forall_operands(it, src)
      collect_objects_rec(*it, ns, dest);
  }
}

/*******************************************************************\

Function: collect_objects

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void collect_objects(
  const goto_programt &src,
  const namespacet &ns,
  std::set<ssa_objectt> &dest)
{
  forall_goto_program_instructions(it, src)
  {
    collect_objects_rec(it->guard, ns, dest);
    collect_objects_rec(it->code, ns, dest);
  }
}

/*******************************************************************\

Function: ssa_objectt::object_id_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

irep_idt ssa_objectt::object_id_rec(
  const exprt &src,
  const namespacet &ns)
{
  if(src.id()==ID_symbol)
  {
    return to_symbol_expr(src).get_identifier();
  }
  else if(src.id()==ID_member)
  {
    const member_exprt &member_expr=to_member_expr(src);
    const exprt &compound_op=member_expr.struct_op();
    const typet &compound_type=ns.follow(compound_op.type());
    
    // need to distinguish union and struct members
    if(compound_type.id()==ID_struct)
    {
      irep_idt compound_object=object_id_rec(compound_op, ns);
      if(compound_object==irep_idt()) return irep_idt();
    
      return id2string(compound_object)+
             "."+id2string(member_expr.get_component_name());
    }
    else if(compound_type.id()==ID_union)
      return irep_idt();
    else
      return irep_idt();
  }
  else if(src.id()==ID_index)
  {
    #if 0
    const index_exprt &index_expr=to_index_expr(src);
    return id2string(object_id_rec(index_expr.array()))+
           "["+"]";
    #else
    return irep_idt();
    #endif
  }
  else if(src.id()==ID_dereference)
  {
    const dereference_exprt &dereference_expr=to_dereference_expr(src);
    irep_idt pointer_object=object_id_rec(dereference_expr.pointer(), ns);
    if(pointer_object==irep_idt()) return irep_idt();
    return id2string(pointer_object)+"'obj";
  }
  else
    return irep_idt();
}

