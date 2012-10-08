/*******************************************************************\

Module: Modular (i.e., per C file) analysis of function pointers.

Author: Ondrej Sery, ondrej.sery@d3s.mff.cuni.cz

\*******************************************************************/

#include <std_expr.h>
#include <context.h>
#include <ansi-c/type2name.h>

#include "modular_fptr_analysis.h"
#include "modular_code_analysis.h"

modular_fptr_analysist::modular_fptr_analysist() : any_variable("__ANY__") 
{
  set_visible(any_variable);
}

modular_fptr_analysist::~modular_fptr_analysist() 
{
}

void
modular_fptr_analysist::accept_function_call(
        const code_function_callt& instruction)
{
  irep_idt function_var = current_function;
  set_visible(function_var);
  const exprt& target = instruction.function();
  
  if (target.id() == ID_symbol) {
    // Direct function call, we just mark the call graph edge
    const symbol_exprt& symbol = to_symbol_expr(target);
    
    std::cout << " - direct call to \"" << 
            symbol.get_identifier() <<
            "\"" << std::endl;
    
    irep_idt function_value = symbol.get_identifier();
    
    add_value(function_var, function_value);
  }
  else if (target.id() == ID_dereference)
  {
    // Indirect call, we find out what is actually dereferenced and add 
    // the dependency on the corresponding "type [x field]"
    std::cout << " - indirect call: " << target.to_string() <<
            std::endl;

    variablet var;
    const dereference_exprt& dereference = to_dereference_expr(target);
            
    if (try_compute_variable(dereference.pointer(), var)) 
    {
      add_rule(function_var, var);
    }
    
    // FIXME: Handle also parameters here -> hard to do due to yet unknown
    // aliasing.
  } 
  else
  {
    // Unknown function call operand
    assert(false);
  }
}

void
modular_fptr_analysist::accept_assign(const code_assignt& instruction)
{
  std::cout << " - rhs: " << instruction.rhs().to_string() << std::endl;
  
  variablet lhs_var;
  if (!try_compute_variable(instruction.lhs(), lhs_var))
    return;
  
  process_assignment(lhs_var, instruction.rhs());
}

void
modular_fptr_analysist::accept_return(const code_returnt& instruction)
{
  std::cout << " - return value: " << instruction.return_value().to_string() <<
          std::endl;
  variablet lhs_var = current_function.as_string() + ".return_value";
  
  process_assignment(lhs_var, instruction.return_value());
}

void
modular_fptr_analysist::process_assignment(const variablet& lhs_var, 
        const exprt& rhs)
{
  valuet rhs_val;
  variablet rhs_var;
  
  if (try_compute_constant_value(rhs, rhs_val)) 
  {
    add_value(lhs_var, rhs_val);
  }
  else 
  {
    if (try_compute_variable(rhs, rhs_var))
    {
      add_rule(lhs_var, rhs_var);
    }
  }
}

bool
modular_fptr_analysist::try_compute_constant_value(const exprt& expr, 
        valuet& value)
{
  if (expr.id() == ID_typecast)
  {
    return try_compute_constant_value(expr.op0(), value);
  }
  else if (expr.id() == ID_address_of)
  {
    const address_of_exprt& address_of = to_address_of_expr(expr);
    
    if (expr.type().id() == ID_pointer && 
            expr.type().subtype().id() == ID_code &&
            address_of.object().id() == ID_symbol)
    {
      // A constant function pointer (i.e., an address of a function)
      value = to_symbol_expr(address_of.object()).get_identifier();
      return true;
    }
  }
  return false;
}

bool
modular_fptr_analysist::try_compute_symbol_variable(const exprt& expr, 
        variablet& variable)
{
  assert(context);
  
  if(expr.id() == ID_symbol) 
  {
    // Directly a symbol
    irep_idt id = to_symbol_expr(expr).get_identifier();
    const symbolt& symbol = context->lookup(id);
    
    if(symbol.is_lvalue) 
    {
      variable = id;
      
      if (is_symbol_visible(symbol))
        set_visible(variable);
      
      return true;
    }
  } 
  else if (expr.id() == ID_member)
  {
    // A field of a structure
    const member_exprt& member = to_member_expr(expr);
    
    if(member.struct_op().id() == ID_symbol) 
    {
      irep_idt id = to_symbol_expr(member.struct_op()).get_identifier();
      const symbolt& symbol = context->lookup(id);
    
      if(symbol.is_lvalue) 
      {
        variable = id.as_string() + "." + member.get_component_name().as_string();
        
        if (is_symbol_visible(symbol))
          set_visible(variable);
        
        return true;
      }
    }
  }
  else if (expr.id() == ID_typecast)
  {
    return try_compute_symbol_variable(expr.op0(), variable);
  }
  return false;
}

bool
modular_fptr_analysist::try_compute_field_access_variable(const exprt& expr, 
        variablet& variable)
{
  if (expr.id() == ID_member)
  {
    const member_exprt& member = to_member_expr(expr);
    const typet& struct_type = member.struct_op().type();
    assert(struct_type.id() == ID_symbol);
    
    variable = irep_idt(
            to_symbol_type(struct_type).get_identifier().as_string() + "." +
            member.get_component_name().as_string());
    
    set_visible(variable);
    return true;
  }
  return false;
}

bool 
modular_fptr_analysist::try_compute_type_variable(const exprt& expr, 
        variablet& variable)
{
  const typet& type = expr.type();
  assert(type.id() == ID_pointer);
  
  if (type.id() == ID_pointer && type.subtype().id() == ID_code)
  {
    variable = type2name(to_pointer_type(type));
    set_visible(variable);
    return true;
  }
  return false;
}
  
bool
modular_fptr_analysist::try_compute_variable(const exprt& expr, 
        variablet& variable)
{
  assert(context);
  
  // Ignore any non-pointer expression
  if (expr.type().id() != ID_pointer)
  {
    std::cout << "Ignoring type: " << type2name(expr.type()) << std::endl;
    return false;
  }
  
  variablet prev_var = any_variable;
  variable = prev_var;
  
  if (try_compute_type_variable(expr, variable)) 
  {
    add_rule(prev_var, variable);
    prev_var = variable;
  }
  if (try_compute_field_access_variable(expr, variable)) {
    add_rule(prev_var, variable);
    prev_var = variable;
  }
  if (try_compute_symbol_variable(expr, variable)) {
    add_rule(prev_var, variable);
    prev_var = variable;
  }
  return true;
}

bool
modular_fptr_analysist::is_symbol_visible(const symbolt& symbol)
{
  return symbol.is_static_lifetime && !symbol.is_file_local;
}

bool
modular_fptr_analysist::get_callees(const irep_idt& id, valuest& functions)
{
  functions.clear();
  
  value_mapt::const_iterator it =
          value_map.find(id);
  
  if (it == value_map.end())
    return false;
  
  functions.insert(it->second.begin(), it->second.end());
  
  return functions.size() != 0;
}
