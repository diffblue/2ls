/*******************************************************************\

Module: SSA

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/i2string.h>
#include <util/expr_util.h>

#include <langapi/language_util.h>

#include "function_ssa.h"

/*******************************************************************\

Function: function_SSAt::build_source_map

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void function_SSAt::build_source_map(const goto_functiont &goto_function)
{
}

/*******************************************************************\

Function: function_SSAt::build_SSA

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void function_SSAt::build_SSA(const goto_functiont &goto_function)
{
  exprt guard=guard_symbol();

  forall_goto_program_instructions(i_it, goto_function.body)
  {
    if(i_it->is_assign())
    {
      const code_assignt &code_assign=to_code_assign(i_it->code);
    
      nodes.push_back(nodet());
      nodet &n=nodes.back();
      n.guard=rename(guard);

      // order matters here, RHS is done before LHS
      n.equality.rhs()=rename(code_assign.rhs());
      n.equality.lhs()=assign(code_assign.lhs());
    }
    else if(i_it->is_goto())
    {
      // changes the guard
      nodes.push_back(nodet());
      nodet &n=nodes.back();
      n.guard=rename(guard);
    
      // order matters here, RHS is done before LHS
      n.equality.rhs()=rename(and_exprt(guard, i_it->guard));
      n.equality.lhs()=assign(guard);
    }
    else if(i_it->is_function_call())
    {
      const code_function_callt &code_function_call=
        to_code_function_call(i_it->code);

      if(code_function_call.lhs().is_not_nil())
      {
        #if 0
        nodes.push_back(nodet());
        nodet &n=nodes.back();
        n.guard=rename(guard);

        // order matters here, RHS is done before LHS
        n.equality.rhs()=rename(code_assign.rhs());
        n.equality.lhs()=assign(code_function_call.lhs());
        #endif
      }
    }
    else if(i_it->is_return())
    {
    }
    else if(i_it->is_assume())
    {
    }
    else if(i_it->is_assert())
    {
    }
  }
}

/*******************************************************************\

Function: function_SSAt::guard_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

symbol_exprt function_SSAt::guard_symbol()
{
  return symbol_exprt("ssa::$guard", bool_typet());
}

/*******************************************************************\

Function: function_SSAt::rename

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt function_SSAt::rename(const exprt &expr)
{
  if(expr.id()==ID_symbol)
  {
    symbol_exprt symbol_expr=to_symbol_expr(expr); // copy
    const irep_idt &old_id=symbol_expr.get_identifier();
    unsigned cnt=ssa_map[old_id];
    irep_idt new_id=id2string(old_id)+"#"+i2string(cnt)+suffix;
    symbol_expr.set_identifier(new_id);
    return symbol_expr;
  }
  else if(expr.id()==ID_address_of)
  {
    return expr;
  }
  else
  {
    exprt tmp=expr; // copy
    Forall_operands(it, tmp)
      *it=rename(*it);
    return tmp;
  }
}

/*******************************************************************\

Function: function_SSAt::assign

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt function_SSAt::assign(const exprt &expr)
{
  if(expr.id()==ID_symbol)
  {
    const irep_idt &old_id=to_symbol_expr(expr).get_identifier();
    ++ssa_map[old_id];
    return rename(expr);
  }
  else if(expr.id()==ID_index)
  {
    index_exprt index_expr=to_index_expr(expr); // copy
    index_expr.index()=rename(index_expr.index());
    index_expr.array()=assign(index_expr.array());
    return index_expr;
  }
  else if(expr.id()==ID_member)
  {
    member_exprt member_expr=to_member_expr(expr); // copy
    member_expr.struct_op()=assign(member_expr.struct_op());
    return member_expr;
  }
  else if(expr.id()==ID_dereference)
  {
    dereference_exprt dereference_expr=to_dereference_expr(expr); // copy
    
    dereference_expr.pointer()=rename(dereference_expr.pointer());

    return dereference_expr;
  }
  else if(expr.id()==ID_typecast)
  {
    typecast_exprt typecast_expr=to_typecast_expr(expr); //copy
    typecast_expr.op()=assign(typecast_expr.op());
    return typecast_expr;
  }
  else
    return expr;
}

/*******************************************************************\

Function: function_SSAt::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void function_SSAt::output(std::ostream &out)
{
  exprt guard;

  for(nodest::const_iterator
      n_it=nodes.begin(); n_it!=nodes.end(); n_it++)
  {
    if(guard!=n_it->guard)
    {
      guard=n_it->guard;
      out << std::endl;
      out << "[" << from_expr(ns, "", guard) << "]" << std::endl;
    }

    output(*n_it, out);
  }
}

/*******************************************************************\

Function: function_SSAt::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void function_SSAt::output(const nodet &node, std::ostream &out)
{
  out << from_expr(ns, "", node.equality);
  
  out << std::endl;
}

