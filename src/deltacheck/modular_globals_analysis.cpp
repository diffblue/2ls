/*******************************************************************\

Module: Modular (i.e., per C file) analysis of globals.

Author: Ondrej Sery, ondrej.sery@d3s.mff.cuni.cz

\*******************************************************************/

#include <i2string.h>
#include <std_expr.h>
#include <context.h>
#include <symbol.h>

#include "modular_globals_analysis.h"

modular_globals_analysist::modular_globals_analysist()
{
}

modular_globals_analysist::~modular_globals_analysist() 
{
}

bool
modular_globals_analysist::get_aliased_globals(const irep_idt& id, 
        valuest& globals)
{
  assert(context);
  globals.clear();
  
  const typet& type = context->lookup(id).type;
  irep_idt type_id = type_to_string(type);
  
  typename value_mapt::const_iterator it =
          value_map.find(type_id);
  
  if (it == value_map.end())
    return false;
  
  globals.insert(it->second.begin(), it->second.end());
  
  return globals.size() != 0;
}

void
modular_globals_analysist::accept_assign(const code_assignt& instruction)
{
    process_global_dereferences_rec(instruction.rhs());
}

void
modular_globals_analysist::accept_function_call(
        const code_function_callt& instruction)
{
  const code_function_callt::argumentst& args = instruction.arguments();
  
  for(code_function_callt::argumentst::const_iterator it = args.begin();
          it != args.end();
          ++it)
  {
    process_global_dereferences_rec(*it);
  }
}

void
modular_globals_analysist::accept_return(const code_returnt& instruction)
{
  process_global_dereferences_rec(instruction.return_value());
}

bool
modular_globals_analysist::try_compute_value(const exprt& expr, valuet& value)
{
  assert(context);
  if (expr.id() == ID_symbol) 
  {
    irep_idt id = to_symbol_expr(expr).get_identifier();
    const symbolt& symbol = context->lookup(id);
    
    if (symbol.static_lifetime && symbol.lvalue) {
      value = id;
      return true;
    }
  }
  return false;
}

bool
modular_globals_analysist::try_compute_variable(
        const exprt& expr, variablet& variable)
{
  assert(context);
  if (expr.id() == ID_symbol) 
  {
    irep_idt id = to_symbol_expr(expr).get_identifier();
    const symbolt& symbol = context->lookup(id);
    
    if (symbol.static_lifetime && symbol.lvalue)
    {
      variable = type_to_string(symbol.type);
      return true;
    }
  }
  return false;
}

irep_idt
modular_globals_analysist::type_to_string(const typet& type)
{
  if (type.id() == ID_symbol) 
  {
    // Symbol type
    return to_symbol_type(type).get_identifier();
  }
  else if (type.id() == ID_signedbv ||
          type.id() == ID_unsignedbv ||
          type.id() == ID_fixedbv ||
          type.id() == ID_floatbv)
  {
    // FIXME: Better encoding
    return type.id().as_string() + "_" + 
            i2string(to_bitvector_type(type).get_width());
  }
  else 
  {
    return type.id();
  }
}

void
modular_globals_analysist::process_global_dereferences_rec(const exprt& expr)
{
  if (expr.id() == ID_address_of) 
  {
    // Dereference, check if it is a global one
    const address_of_exprt& address_of = to_address_of_expr(expr);
    valuet value;
    variablet variable;
    
    if (try_compute_value(address_of.object(), value) && 
            try_compute_variable(address_of.object(), variable))
    {
      add_value(variable, value);
      return;
    }
  }
  
  // Process everything else recursively
  forall_operands(it, expr)
  {
    process_global_dereferences_rec(*it);
  }
}
