/*******************************************************************\

Module: Symbol Renaming

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "rename.h"

/*******************************************************************\

Function: rename

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void rename(symbol_tablet &symbol_table)
{
}

/*******************************************************************\

Function: rename

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void rename(exprt &expr)
{
  Forall_operands(it, expr)
    rename(*it);
  
  rename(expr.type());
  
  if(expr.id()==ID_symbol)
  {
  }

  if(expr.find(ID_C_c_sizeof_type).is_not_nil())
  {
    irept &c_sizeof_type=expr.add(ID_C_c_sizeof_type);

    if(c_sizeof_type.is_not_nil())
      rename(static_cast<typet &>(c_sizeof_type));
  }
}

/*******************************************************************\

Function: rename

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void rename(typet &type)
{
  if(type.has_subtype())
    rename(type.subtype());

  Forall_subtypes(it, type)
    rename(*it);
    
  if(type.id()==ID_struct ||
     type.id()==ID_union)
  {
    struct_union_typet &struct_union_type=to_struct_union_type(type);
    struct_union_typet::componentst &components=struct_union_type.components();

    for(struct_union_typet::componentst::iterator
        it=components.begin();
        it!=components.end();
        it++)
      rename(*it);
  } 
  else if(type.id()==ID_code)
  {
    code_typet &code_type=to_code_type(type);
    rename(code_type.return_type());

    code_typet::argumentst &arguments=code_type.arguments();

    for(code_typet::argumentst::iterator
        it=arguments.begin();
        it!=arguments.end();
        it++)
    {
      rename(*it);
    }
  }
  else if(type.id()==ID_symbol)
  {
    irep_idt old=type.get(ID_identifier);
  }
  else if(type.id()==ID_array)
  {
    // do the size -- the subtype is already done
    rename(to_array_type(type).size());
  }
}

/*******************************************************************\

Function: rename

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void rename(goto_functionst &)
{

}
