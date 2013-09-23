/*******************************************************************\

Module: Symbol Renaming

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "rename.h"

/*******************************************************************\

Function: renamet::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void renamet::operator()(symbol_tablet &symbol_table)
{
  for(symbol_tablet::symbolst::iterator
      s_it=symbol_table.symbols.begin();
      s_it!=symbol_table.symbols.end();
      s_it++)
  {
    operator()(s_it->second);
  }
}

/*******************************************************************\

Function: renamet::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void renamet::operator()(symbolt &symbol)
{
  operator()(symbol.value);
  operator()(symbol.type);
}

/*******************************************************************\

Function: renamet::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void renamet::operator()(exprt &expr)
{
  Forall_operands(it, expr)
    operator()(*it);
  
  operator()(expr.type());
  
  if(expr.id()==ID_symbol)
  {
    const irep_idt old_name=expr.get(ID_identifier);
    const irep_idt new_name=id2string(old_name)+suffix;
    expr.set(ID_identifier, new_name);
  }

  if(expr.find(ID_C_c_sizeof_type).is_not_nil())
  {
    irept &c_sizeof_type=expr.add(ID_C_c_sizeof_type);

    if(c_sizeof_type.is_not_nil())
      operator()(static_cast<typet &>(c_sizeof_type));
  }
}

/*******************************************************************\

Function: renamet::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void renamet::operator()(typet &type)
{
  if(type.has_subtype())
    operator()(type.subtype());

  Forall_subtypes(it, type)
    operator()(*it);
    
  if(type.id()==ID_struct ||
     type.id()==ID_union)
  {
    struct_union_typet &struct_union_type=to_struct_union_type(type);
    struct_union_typet::componentst &components=struct_union_type.components();

    for(struct_union_typet::componentst::iterator
        it=components.begin();
        it!=components.end();
        it++)
      operator()(*it);
  } 
  else if(type.id()==ID_code)
  {
    code_typet &code_type=to_code_type(type);
    operator()(code_type.return_type());

    code_typet::argumentst &arguments=code_type.arguments();

    for(code_typet::argumentst::iterator
        it=arguments.begin();
        it!=arguments.end();
        it++)
    {
      operator()(*it);
    }
  }
  else if(type.id()==ID_symbol)
  {
    const irep_idt old_name=type.get(ID_identifier);
    const irep_idt new_name=id2string(old_name)+"$old";
    type.set(ID_identifier, new_name);
  }
  else if(type.id()==ID_array)
  {
    // do the size -- the subtype is already done
    operator()(to_array_type(type).size());
  }
}

/*******************************************************************\

Function: renamet::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void renamet::operator()(goto_functionst &goto_functions)
{
  for(goto_functionst::function_mapt::iterator
      f_it=goto_functions.function_map.begin();
      f_it!=goto_functions.function_map.end();
      f_it++)
    operator()(f_it->second);
}

/*******************************************************************\

Function: renamet::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void renamet::operator()(goto_functionst::goto_functiont &goto_function)
{
  operator()(goto_function.type);
  
  Forall_goto_program_instructions(i_it, goto_function.body)
  {
    operator()(i_it->code);
    operator()(i_it->guard);
  }
}
