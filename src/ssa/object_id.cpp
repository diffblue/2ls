/*******************************************************************\

Module: Strings from Objects

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/std_expr.h>

#include "object_id.h"

/*******************************************************************\

Function: object_id

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

irep_idt object_id(const exprt &src)
{
  if(src.id()==ID_symbol)
  {
    return to_symbol_expr(src).get_identifier();
  }
  else if(src.id()==ID_member)
  {
    const member_exprt &member_expr=to_member_expr(src);
    
    if(member_expr.struct_op().id()==ID_dereference)
    {
      const dereference_exprt &dereference_expr=
        to_dereference_expr(member_expr.struct_op());

      return id2string(object_id(dereference_expr.pointer()))+"->"+
             id2string(member_expr.get_component_name());
    }
    else   
      return id2string(object_id(member_expr.struct_op()))+"."+
             id2string(member_expr.get_component_name());
  }
  else if(src.id()==ID_index)
  {
    const index_exprt &index_expr=to_index_expr(src);
    return id2string(object_id(index_expr.array()))+
           "["+"]";
  }
  else if(src.id()==ID_dereference)
  {
    const dereference_exprt &dereference_expr=to_dereference_expr(src);
    irep_idt pointer_object=object_id(dereference_expr.pointer());
    if(pointer_object==irep_idt()) return irep_idt();
    return id2string(pointer_object)+"->*";
  }
  else
    return irep_idt();
}

