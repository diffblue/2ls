/*******************************************************************\

Module: Call graph builder, builds and stores partial call graphs
(per C file).

Author: Ondrej Sery, ondrej.sery@d3s.mff.cuni.cz

\*******************************************************************/

#include "cgraph_builder.h"

#include <iostream>
#include <std_expr.h>

cgraph_buildert::cgraph_buildert()
{
}

void
cgraph_buildert::analyze_module(const goto_functionst& functions) 
{
  forall_goto_functions(it, functions) 
  {
    const goto_functionst::goto_functiont& function = it->second;
    
    if (function.body_available) 
    {
      std::cout << "=================================" << std::endl;
      std::cout << "Analyzing function: " << it->first << std::endl;
      analyze_function(it->first, function);
    }
  }
  
  partial_analysis.find_fixpoint();
  // TODO
  // partial_analysis.remove_invisible();
}

void
cgraph_buildert::analyze_function(
        irep_idt current_function,
        const goto_functionst::goto_functiont& function)
{
  forall_goto_program_instructions(it, function.body)
  {
    analyze_instruction(current_function, *it);
  }
}

void
cgraph_buildert::analyze_instruction(
        irep_idt current_function,
        const goto_programt::instructiont& instr)
{
  switch(instr.type) {
    case FUNCTION_CALL:
      // A function call, note this in the call graph
      std::cout << "Function call at: " << instr.location.to_string() << std::endl;
      analyze_function_call(current_function, to_code_function_call(instr.code));
      break;
    case ASSIGN:
      // Check for any use of function addresses
      std::cout << "Assignment at: " << instr.location.to_string() << std::endl;
      analyze_assignment(to_code_assign(instr.code));
      break;
    default:
      // Nothing relevant in the other instructions
      break;
  }
}

void
cgraph_buildert::analyze_function_call(
        irep_idt current_function,
        const code_function_callt& function_call)
{
  irep_idt function_var = current_function;
  partial_analysis.set_visible(function_var);
  
  if (function_call.function().id() == ID_symbol) {
    // TODO: Direct function call, we just mark the call graph edge
    const symbol_exprt& symbol = to_symbol_expr(function_call.function());
    
    std::cout << " - direct call to \"" << 
            symbol.get_identifier() <<
            "\"" << std::endl;
    
    irep_idt function_value = symbol.get_identifier();
    
    partial_analysis.add_value(function_var, function_value);
  }
  else
  {
    // TODO: Indirect call, we find out what is actually dereferenced and add 
    // the dependency on the corresponding "type [x field]"
    std::cout << " - indirect call: " << function_call.function().to_string() <<
            std::endl;

    irep_idt var = compute_variable_name(function_call.function());
    
    partial_analysis.add_rule(function_var, var);
  }
}

void
cgraph_buildert::analyze_assignment(const code_assignt& assignment)
{
  // TODO: See whether there is a function address computed.
  // If so, it has to be added to the set of functions addressable by 
  // the corresponding "type [x field]"
  std::cout << " - rhs: " << assignment.rhs().to_string() << std::endl;
  
  irep_idt rhs_var = compute_variable_name(assignment.rhs());
  irep_idt lhs_var = compute_variable_name(assignment.lhs());
  
  partial_analysis.add_rule(lhs_var, rhs_var);
  
  // TODO: The following is not addressed at all:
  // - non-scalar assignment: structures, arrays, etc.
  // - "normal" pointer aliasing
}

irep_idt
cgraph_buildert::compute_variable_name(const exprt& expr) const
{
  // TODO: Implement translation of expressions to variables for fixpoint
  // analysis
  return "UNIMPLEMENTED";
}



