/*******************************************************************\

Module: Modular (i.e., per C file) analysis of globals.

Author: Ondrej Sery, ondrej.sery@d3s.mff.cuni.cz

\*******************************************************************/

#include <i2string.h>
#include <std_expr.h>
#include <symbol_table.h>
#include <symbol.h>
#include <ansi-c/type2name.h>

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
  assert(symbol_table);
  globals.clear();
  
  const typet& type = symbol_table->lookup(id).type;
  irep_idt type_id = type2name(type);
  
  value_mapt::const_iterator it =
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
  assert(symbol_table);
  if (expr.id() == ID_symbol) 
  {
    irep_idt id = to_symbol_expr(expr).get_identifier();
    const symbolt& symbol = symbol_table->lookup(id);
    
    if(symbol.is_static_lifetime && symbol.is_lvalue)
    {
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
  assert(symbol_table);
  if (expr.id() == ID_symbol) 
  {
    irep_idt id = to_symbol_expr(expr).get_identifier();
    const symbolt& symbol = symbol_table->lookup(id);
    
    if(symbol.is_static_lifetime && symbol.is_lvalue)
    {
      variable = type2name(symbol.type);
      set_visible(variable);
      return true;
    }
  }
  return false;
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
