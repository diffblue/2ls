/*******************************************************************\

Module: SSA for malloc()

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/std_types.h>
#include <util/std_expr.h>
#include <util/arith_tools.h>
#include <util/expr_util.h>
#include <util/symbol.h>
#include <util/i2string.h>
#include <util/pointer_offset_size.h>

#include <ansi-c/c_types.h>

#include "malloc_ssa.h"

/*******************************************************************\

Function: 

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

inline static typet c_sizeof_type_rec(const exprt &expr)
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
      typet t=c_sizeof_type_rec(*it);
      if(t.is_not_nil()) return t;
    }
  }
  
  return nil_typet();
}

/*******************************************************************\

Function: malloc_ssa

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt malloc_ssa(
  const side_effect_exprt &code,
  const std::string &suffix,
  symbol_tablet &symbol_table)
{
  if(code.operands().size()!=1)
    throw "malloc expected to have one operand";

  namespacet ns(symbol_table);
  exprt size=code.op0();
  typet object_type=nil_typet();
  
  {
    // special treatment for sizeof(T)*x
    if(size.id()==ID_mult &&
       size.operands().size()==2 &&
       size.op0().find(ID_C_c_sizeof_type).is_not_nil())
    {
      object_type=array_typet(
        c_sizeof_type_rec(size.op0()),
        size.op1());      
    }
    else if(size.id()==ID_mult &&
       size.operands().size()==2 &&
       size.op1().find(ID_C_c_sizeof_type).is_not_nil())
    {
      object_type=array_typet(
        c_sizeof_type_rec(size.op1()),
        size.op0());      
    }
    else
    {
      typet tmp_type=c_sizeof_type_rec(size);
      
      if(tmp_type.is_not_nil())
      {
        // Did the size get multiplied?
        mp_integer elem_size=pointer_offset_size(tmp_type, ns);
        mp_integer alloc_size;
        if(elem_size<0 || to_integer(size, alloc_size))
        {
        }
        else
        {
          if(alloc_size==elem_size)
            object_type=tmp_type;
          else
          {
            mp_integer elements=alloc_size/elem_size;
            
            if(elements*elem_size==alloc_size)
              object_type=array_typet(tmp_type, from_integer(elements, size.type()));
          }
        }
      }
    }

    // the fall-back is to produce a byte-array    
    if(object_type.is_nil())
      object_type=array_typet(unsigned_char_type(), size);
  }

#ifdef DEBUG
  std::cout << "OBJECT_TYPE: " << from_type(ns, "", object_type) << std::endl;
#endif
  
  // value
  symbolt value_symbol;
  
  value_symbol.base_name="dynamic_object"+suffix;
  value_symbol.name="ssa::"+id2string(value_symbol.base_name);
  value_symbol.is_lvalue=true;
  value_symbol.type=object_type;
  value_symbol.type.set("#dynamic", true);
  value_symbol.mode=ID_C;
  symbol_table.add(value_symbol);

  address_of_exprt address_of;
  
  if(object_type.id()==ID_array)
  {
    address_of.type()=pointer_typet(value_symbol.type.subtype());
    index_exprt index_expr(value_symbol.type.subtype());
    index_expr.array()=value_symbol.symbol_expr();
    index_expr.index()=gen_zero(index_type());
    address_of.op0()=index_expr;
  }
  else
  {
    address_of.op0()=value_symbol.symbol_expr();
    address_of.type()=pointer_typet(value_symbol.type);
  }
  
  exprt result=address_of;
  
  if(result.type()!=code.type())
    result=typecast_exprt(result, code.type());

  return result;
}


static void replace_malloc_rec(exprt &expr,
         		const std::string &suffix,
			symbol_tablet &symbol_table,
                        const exprt &malloc_size,
                        unsigned &counter)
{
  if(expr.id()==ID_side_effect &&
     to_side_effect_expr(expr).get_statement()==ID_malloc)
  {
    assert(!malloc_size.is_nil());
    expr.op0() = malloc_size;
 
    expr = malloc_ssa(to_side_effect_expr(expr),"$"+i2string(counter++)+suffix,symbol_table);
  }
  else
    Forall_operands(it,expr)
      replace_malloc_rec(*it,suffix,symbol_table,malloc_size,counter);
}

void replace_malloc(goto_modelt &goto_model,
		    const std::string &suffix)
{
  unsigned counter = 0;
  Forall_goto_functions(f_it, goto_model.goto_functions)
  {
    exprt malloc_size = nil_exprt();
    Forall_goto_program_instructions(i_it, f_it->second.body)
    {
      if(i_it->is_assign())
      {
        code_assignt &code_assign = to_code_assign(i_it->code);
	if(code_assign.lhs().id()==ID_symbol)
	{
          // we have to propagate the malloc size 
          //   in order to get the object type
	  // TODO: this only works with inlining
	  const irep_idt &lhs_id = 
	    to_symbol_expr(code_assign.lhs()).get_identifier();
	  if(lhs_id == "malloc::malloc_size")
	    malloc_size = code_assign.rhs();
	}
        replace_malloc_rec(code_assign.rhs(),suffix,
			   goto_model.symbol_table,malloc_size,counter);
      }
    }
  }
}

