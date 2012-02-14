/*******************************************************************\

Module: Call graph builder, builds and stores partial call graphs
(per C file).

Author: Ondrej Sery, ondrej.sery@d3s.mff.cuni.cz

\*******************************************************************/

#include "cgraph_builder.h"

#include <string>
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
  
  std::cout << "===== AFTER COLLECTION =====" << std::endl;
  partial_analysis.print(std::cout);
  partial_analysis.find_fixpoint();
  std::cout << "===== AFTER FIXPOINT =====" << std::endl;
  partial_analysis.print(std::cout);
  partial_analysis.remove_invisible();
  std::cout << "===== AFTER FILTERING =====" << std::endl;
  partial_analysis.print(std::cout);
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
  
  irep_idt lhs_var = compute_variable_name(assignment.lhs());
  const exprt& rhs = assignment.rhs();
  
  // A constant function pointer?
  if (rhs.id() == ID_address_of && 
          rhs.type().id() == ID_pointer && 
          rhs.type().subtype().id() == ID_code) {
    assert (rhs.operands().size() == 1);
    assert (rhs.op0().id() == ID_symbol);
    
    partial_analysis.add_value(lhs_var,
            to_symbol_expr(rhs.op0()).get_identifier());
    return;
  }
  
  irep_idt rhs_var = compute_variable_name(rhs);
  partial_analysis.add_rule(lhs_var, rhs_var);
  
  // TODO: The following is not addressed at all:
  // - non-scalar assignment: structures, arrays, etc.
  // - "normal" pointer aliasing
}

irep_idt
cgraph_buildert::compute_variable_name(const exprt& expr)
{
  // TODO: Implement translation of expressions to variables for fixpoint
  // analysis
  if (expr.id() == ID_symbol) 
  {
    const symbol_exprt& symbol = to_symbol_expr(expr);
    return symbol.get_identifier();
  } 
  else if (expr.id() == ID_address_of)
  {
    assert(expr.operands().size() == 1);
    const address_of_exprt& address_of = to_address_of_expr(expr);
    
    // Is it a function pointer?
    if (expr.type().id() == ID_pointer && 
            expr.type().subtype().id() == ID_code)
    {
      const exprt &op = address_of.op0();
      
      // A constant function pointer (i.e., an address of a function)?
      if (op.id() == ID_symbol)
        return to_symbol_expr(op).get_identifier();
    }
  }
  else if (expr.id() == ID_dereference)
  {
    assert(expr.operands().size() == 1);
    const dereference_exprt& dereference = to_dereference_expr(expr);
    const exprt &op = dereference.op0();
    
    // Dereferencing a symbol?
    //if (op.id() == ID_symbol)
    //  return to_symbol_expr(op).get_identifier();
    return compute_variable_name(op);
  }
  else if (expr.id() == ID_member)
  {
    const member_exprt& member = to_member_expr(expr);
    const typet& struct_type = member.struct_op().type();
    assert(struct_type.id() == ID_symbol);
    
    irep_idt res_var(
            to_symbol_type(struct_type).get_identifier().as_string() + "." +
            member.get_component_name().c_str());
    
    partial_analysis.set_visible(res_var);
    
    return res_var;
  }
  return "UNIMPLEMENTED";
}

void
cgraph_buildert::serialize(const std::string& file_name)
{
  std::ofstream out(file_name.c_str());
  if (!out)
    throw "Failed to write the partial call graph file: " + file_name;
  
  partial_analysis.serialize(out);
  
  if (!out)
  {
    out.close();
    throw "Failed to write the partial call graph file: " + file_name;
  }
  out.close();
}

void
cgraph_buildert::deserialize(const std::string& file_name)
{
  std::ifstream in(file_name.c_str());
  if (!in)
    throw "Failed to read the partial call graph file: " + file_name;
  
  partial_analysis.deserialize(in);
  
  if (!in)
  {
    in.close();
    throw "Failed to read the partial call graph file: " + file_name;
  }
  in.close();
}

void
cgraph_buildert::deserialize_list(std::istream& in)
{
  std::string line_str;
  
  while (getline(in, line_str))
  {
    if (!line_str.empty())
      deserialize(line_str + ".dc");
  }
  
  if (in.bad())
  {
    throw "Failed to read the list of call graph files.";
  }
  
  std::cout << "===== AFTER LOAD =====" << std::endl;
  partial_analysis.print(std::cout);
  partial_analysis.find_fixpoint();
  std::cout << "===== AFTER FIXPOINT =====" << std::endl;
  partial_analysis.print(std::cout);
}
