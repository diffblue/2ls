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
  std::set<ssa_objectt> &dest)
{
  const typet &type=ns.follow(src.type());

  if(type.id()==ID_code)
    return;

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

  irep_idt id=object_id(src);
  
  if(id!=irep_idt())
    dest.insert(ssa_objectt(src));
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
