/*******************************************************************\

Module: Modular (i.e., per C file) analysis of function pointers.

Author: Ondrej Sery, ondrej.sery@d3s.mff.cuni.cz

\*******************************************************************/

#include <std_expr.h>

#include "modular_fptr_analysis.h"
#include "modular_code_analysis.h"

modular_fptr_analysist::modular_fptr_analysist() {
}

modular_fptr_analysist::~modular_fptr_analysist() {
}

void
modular_fptr_analysist::accept_function_call(
        const code_function_callt& instruction)
{
  irep_idt function_var = current_function;
  set_visible(function_var);
  
  if (instruction.function().id() == ID_symbol) {
    // Direct function call, we just mark the call graph edge
    const symbol_exprt& symbol = to_symbol_expr(instruction.function());
    
    std::cout << " - direct call to \"" << 
            symbol.get_identifier() <<
            "\"" << std::endl;
    
    irep_idt function_value = symbol.get_identifier();
    
    add_value(function_var, function_value);
  }
  else
  {
    // Indirect call, we find out what is actually dereferenced and add 
    // the dependency on the corresponding "type [x field]"
    std::cout << " - indirect call: " << instruction.function().to_string() <<
            std::endl;

    variablet var;
    if (try_compute_variable(instruction.function(), var)) {
      add_rule(function_var, var);
    }
  }
}

void
modular_fptr_analysist::accept_assign(const code_assignt& instruction)
{
  std::cout << " - rhs: " << instruction.rhs().to_string() << std::endl;
  
  variablet lhs_var;
  if (!try_compute_variable(instruction.lhs(), lhs_var))
    return;
  
  const exprt& rhs = instruction.rhs();
  valuet rhs_val;
  variablet rhs_var;
  
  // FIXME: The following is not addressed at all:
  // - non-scalar assignment: structures, arrays, etc.
  // - "normal" pointer aliasing

  if (try_compute_value(rhs, rhs_val)) 
  {
    add_value(lhs_var, to_symbol_expr(rhs.op0()).get_identifier());
  }
  else 
  {
    if (!try_compute_variable(rhs, rhs_var))
      return;
  
    add_rule(lhs_var, rhs_var);
  }
}

bool
modular_fptr_analysist::try_compute_value(const exprt& expr, valuet& value)
{
  if (expr.id() == ID_address_of)
  {
    assert(expr.operands().size() == 1);
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
modular_fptr_analysist::try_compute_variable(const exprt& expr, 
        variablet& variable)
{
  // Implement translation of expressions to variables for fixpoint
  // analysis
  if (expr.id() == ID_symbol) 
  {
    const symbol_exprt& symbol = to_symbol_expr(expr);
    
    variable = symbol.get_identifier();
    return true;
  } 
  else if (expr.id() == ID_address_of)
  {
    assert(expr.operands().size() == 1);
    const address_of_exprt& address_of = to_address_of_expr(expr);
    
    if (expr.type().id() == ID_pointer && 
            expr.type().subtype().id() == ID_code &&
            address_of.object().id() == ID_symbol)
    {
      // A constant function pointer (i.e., an address of a function)
      // This is a constant value not a variable --> fail the attempt
      return false;
    }
    return try_compute_variable(address_of.object(), variable);
  }
  else if (expr.id() == ID_dereference)
  {
    assert(expr.operands().size() == 1);
    const dereference_exprt& dereference = to_dereference_expr(expr);
    const exprt &op = dereference.pointer();
    
    // Dereferencing a symbol?
    //if (op.id() == ID_symbol)
    //  return to_symbol_expr(op).get_identifier();
    return try_compute_variable(op, variable);
  }
  else if (expr.id() == ID_member)
  {
    const member_exprt& member = to_member_expr(expr);
    const typet& struct_type = member.struct_op().type();
    assert(struct_type.id() == ID_symbol);
    
    variable = irep_idt(
            to_symbol_type(struct_type).get_identifier().as_string() + "." +
            member.get_component_name().c_str());
    
    set_visible(variable);
    return true;
  }
  variable = "UNIMPLEMENTED";
  return true;
}
