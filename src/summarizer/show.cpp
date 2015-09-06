/*******************************************************************\

Module: Showing various debugging information

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/options.h>
#include <util/find_symbols.h>
#include <util/i2string.h>
#include <util/string2int.h>
#include <solvers/prop/prop_conv.h>

#include <goto-programs/read_goto_binary.h>
#include <goto-programs/goto_model.h>
#include <goto-programs/show_properties.h>
#include <goto-programs/set_properties.h>

#include "../ssa/ssa_domain.h"
#include "../ssa/guard_map.h"
#include "../ssa/local_ssa.h"
#include "../ssa/simplify_ssa.h"
#include "../ssa/ssa_value_set.h"

#include "../domains/ssa_fixed_point.h"

#include "summary.h"

/*******************************************************************\

Function: show_assignments

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void show_assignments(
  const goto_functionst::goto_functiont &goto_function,
  const namespacet &ns,
  std::ostream &out)
{
  ssa_objectst ssa_objects(goto_function, ns);
  ssa_value_ait ssa_value_ai(goto_function, ns);
  assignmentst assignments(goto_function.body, ns, ssa_objects, ssa_value_ai);
  assignments.output(ns, goto_function.body, out);
}

/*******************************************************************\

Function: show_assignments

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void show_assignments(
  const goto_modelt &goto_model,
  const irep_idt &function,
  std::ostream &out,
  message_handlert &message_handler)
{
  const namespacet ns(goto_model.symbol_table);

  if(!function.empty())
  {
    goto_functionst::function_mapt::const_iterator
      f_it=goto_model.goto_functions.function_map.find(function);
    if(f_it==goto_model.goto_functions.function_map.end())
      out << "function " << function << " not found\n";
    else
      show_assignments(f_it->second, ns, out);
  }
  else
  {
    forall_goto_functions(f_it, goto_model.goto_functions)
    {
      out << ">>>> Function " << f_it->first << "\n";
            
      show_assignments(f_it->second, ns, out);
        
      out << "\n";
    }
  }
}

/*******************************************************************\

Function: show_defs

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void show_defs(
  const goto_functionst::goto_functiont &goto_function,
  const namespacet &ns,
  std::ostream &out)
{
  ssa_objectst ssa_objects(goto_function, ns);
  ssa_value_ait ssa_value_ai(goto_function, ns);
  assignmentst assignments(goto_function.body, ns, ssa_objects, ssa_value_ai);
  ssa_ait ssa_analysis(assignments);
  ssa_analysis(goto_function, ns);
  ssa_analysis.output(ns, goto_function.body, out);
}

/*******************************************************************\

Function: show_defs

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void show_defs(
  const goto_modelt &goto_model,
  const irep_idt &function,
  std::ostream &out,
  message_handlert &message_handler)
{
  const namespacet ns(goto_model.symbol_table);
  
  if(!function.empty())
  {
    goto_functionst::function_mapt::const_iterator
      f_it=goto_model.goto_functions.function_map.find(function);
    if(f_it==goto_model.goto_functions.function_map.end())
      out << "function " << function << " not found\n";
    else
      show_defs(f_it->second, ns, out);
  }
  else
  {
    forall_goto_functions(f_it, goto_model.goto_functions)
    {
      out << ">>>> Function " << f_it->first << "\n";
          
      show_defs(f_it->second, ns, out);
      
      out << "\n";
    }
  }
}

/*******************************************************************\

Function: show_guards

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void show_guards(
  const goto_functionst::goto_functiont &goto_function,
  const namespacet &ns,
  std::ostream &out)
{
  guard_mapt guard_map(goto_function.body);
  guard_map.output(goto_function.body, out);
}

/*******************************************************************\

Function: show_guards

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void show_guards(
  const goto_modelt &goto_model,
  const irep_idt &function,
  std::ostream &out,
  message_handlert &message_handler)
{
  const namespacet ns(goto_model.symbol_table);
  
  if(!function.empty())
  {
    goto_functionst::function_mapt::const_iterator
      f_it=goto_model.goto_functions.function_map.find(function);
    if(f_it==goto_model.goto_functions.function_map.end())
      out << "function " << function << " not found\n";
    else
      show_guards(f_it->second, ns, out);
  }
  else
  {
    forall_goto_functions(f_it, goto_model.goto_functions)
    {
      out << ">>>> Function " << f_it->first << "\n";
          
      show_guards(f_it->second, ns, out);
      
      out << "\n";
    }
  }
}

/*******************************************************************\

Function: show_ssa

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void show_ssa(
  const goto_functionst::goto_functiont &goto_function,
  bool simplify,
  const namespacet &ns,
  std::ostream &out)
{
  local_SSAt local_SSA(goto_function, ns);
  if(simplify) ::simplify(local_SSA, ns);
  local_SSA.output_verbose(out);
}

/*******************************************************************\

Function: show_ssa

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void show_ssa(
  const goto_modelt &goto_model,
  const irep_idt &function,
  bool simplify,
  std::ostream &out,
  message_handlert &message_handler)
{
  const namespacet ns(goto_model.symbol_table);
  
  if(!function.empty())
  {
    out << ">>>> Function " << function << "\n";
    goto_functionst::function_mapt::const_iterator
      f_it=goto_model.goto_functions.function_map.find(function);
    if(f_it==goto_model.goto_functions.function_map.end())
      out << "function " << function << " not found\n";
    else
      show_ssa(f_it->second, simplify, ns, out);
  }
  else
  {
    forall_goto_functions(f_it, goto_model.goto_functions)
    {
      if(f_it->first=="assert") continue;
      if(f_it->first=="__CPROVER_assume") continue;

      out << ">>>> Function " << f_it->first << "\n";
          
      show_ssa(f_it->second, simplify, ns, out);
      
      out << "\n";
    }
  }
}

/*******************************************************************\

Function: show_fixed_point

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void show_fixed_point(
  const goto_functionst::goto_functiont &goto_function,
  bool simplify,
  const namespacet &ns,
  std::ostream &out)
{
  local_SSAt local_SSA(goto_function, ns);
  if(simplify) ::simplify(local_SSA, ns);
  ssa_fixed_point(local_SSA);
  local_SSA.output(out);
}

/*******************************************************************\

Function: show_fixed_points

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void show_fixed_points(
  const goto_modelt &goto_model,
  const irep_idt &function,
  bool simplify,
  std::ostream &out,
  message_handlert &message_handler)
{
  const namespacet ns(goto_model.symbol_table);
  
  if(!function.empty())
  {
    goto_functionst::function_mapt::const_iterator
      f_it=goto_model.goto_functions.function_map.find(function);
    if(f_it==goto_model.goto_functions.function_map.end())
      out << "function " << function << " not found\n";
    else
      show_fixed_point(f_it->second, simplify, ns, out);
  }
  else
  {
    forall_goto_functions(f_it, goto_model.goto_functions)
    {
      out << ">>>> Function " << f_it->first << "\n";
          
      show_fixed_point(f_it->second, simplify, ns, out);
      
      out << "\n";
    }
  }
}

/*******************************************************************\

Function: show_error_trace

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void print_symbol_values(const local_SSAt &SSA, 
		prop_convt &solver,
		std::ostream &out,
	        const exprt &expr)
{
//  if(expr.id()==ID_symbol)
  {
    out << from_expr(SSA.ns, "",expr) << " == " << 
      from_expr(SSA.ns, "", solver.get(expr)) << "\n";
    //  return;
  }
  for(exprt::operandst::const_iterator it = expr.operands().begin();
      it != expr.operands().end(); it++)
  {
    print_symbol_values(SSA,solver,out,*it);
  }
}

void show_error_trace(const irep_idt &property_id, 
		const local_SSAt &SSA, 
		prop_convt &solver,
		std::ostream &out,
		message_handlert &message_handler)

{
  out << "\n*** Error trace for property " << property_id << "\n";  
  for (local_SSAt::nodest::const_iterator n_it =
     SSA.nodes.begin(); n_it != SSA.nodes.end(); n_it++) 
  {
    for (local_SSAt::nodet::equalitiest::const_iterator e_it =
	   n_it->equalities.begin(); e_it != n_it->equalities.end(); e_it++) 
    {
      print_symbol_values(SSA,solver,out,*e_it);
      // out << from_expr(SSA.ns, "", e_it->op0()) << " == " << 
      //    from_expr(SSA.ns, "", solver.get(e_it->op0())) << "\n";
    }
    for (local_SSAt::nodet::constraintst::const_iterator c_it =
	   n_it->constraints.begin(); c_it != n_it->constraints.end(); c_it++) 
    {
      print_symbol_values(SSA,solver,out,*c_it);
    }
    for (local_SSAt::nodet::assertionst::const_iterator a_it =
	   n_it->assertions.begin(); a_it != n_it->assertions.end(); a_it++) 
    {
      print_symbol_values(SSA,solver,out,*a_it);
    }
  }
  out << "\n";
}

/*******************************************************************\

Function: show_invariants

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

local_SSAt::locationt find_loc_by_guard(const local_SSAt &SSA,
					const symbol_exprt &guard)
{
  std::string gstr = id2string(guard.get_identifier());
  unsigned pos1 = gstr.find("#")+1;
  unsigned pos2 = gstr.find("%",pos1);
  unsigned n = safe_string2unsigned(gstr.substr(pos1,pos2));
  return SSA.find_location_by_number(n);
}

void purify_identifiers(exprt &expr)
{
  if(expr.id()==ID_symbol)
  {
    std::string idstr = id2string(to_symbol_expr(expr).get_identifier());
    to_symbol_expr(expr).set_identifier(idstr.substr(0,idstr.find("#")));
  }
  for(unsigned i=0; i<expr.operands().size(); i++)
  {
    purify_identifiers(expr.operands()[i]);
  }
}

void show_invariant(const local_SSAt &SSA, 
		const exprt &expr,
		std::ostream &out)
{
  //expected format (/\_j g_j) => inv
  const exprt &impl = expr.op0();
  exprt inv = expr.op1(); //copy
  local_SSAt::locationt loc;
  if(impl.id()==ID_symbol)
  {
    loc = find_loc_by_guard(SSA,to_symbol_expr(impl));
  }
  else if(impl.id()==ID_and)
  {
    assert(impl.op0().id()==ID_symbol);
    loc = find_loc_by_guard(SSA,to_symbol_expr(impl.op0()));
  }
  else assert(false);

  out << "\n** invariant: " << loc->source_location << "\n";
  purify_identifiers(inv);
  out << "  " << from_expr(SSA.ns,"",inv) << "\n";
}

void show_invariants(const local_SSAt &SSA, 
		const summaryt &summary,
		std::ostream &out)
{
  if(summary.fw_invariant.is_nil()) return;
  if(summary.fw_invariant.is_true()) return;

  //expected format /\_i g_i => inv_i
  if(summary.fw_invariant.id()==ID_implies)
  {
    show_invariant(SSA,summary.fw_invariant,out);
  }
  else if(summary.fw_invariant.id()==ID_and)
  {
    for(unsigned i=0; i<summary.fw_invariant.operands().size(); i++)
    {
      assert(summary.fw_invariant.operands()[i].id()==ID_implies);
      show_invariant(SSA,summary.fw_invariant.operands()[i],out);
    }
  }
  else assert(false);
}


/*******************************************************************\

Function: show_ssa_symbols

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void show_ssa_symbols(
  const local_SSAt &SSA, 
  std::ostream & out)
{
  std::set<symbol_exprt> symbols;
  out << "\n*** SSA Symbols " << "\n";  
  for (local_SSAt::nodest::const_iterator n_it =
     SSA.nodes.begin(); n_it != SSA.nodes.end(); n_it++) 
  {
    for (local_SSAt::nodet::equalitiest::const_iterator e_it =
	   n_it->equalities.begin(); e_it != n_it->equalities.end(); e_it++) 
    {
      find_symbols(*e_it,symbols);
    }
    for (local_SSAt::nodet::constraintst::const_iterator c_it =
	   n_it->constraints.begin(); c_it != n_it->constraints.end(); c_it++) 
    {
      find_symbols(*c_it,symbols);
    }
    for (local_SSAt::nodet::assertionst::const_iterator a_it =
	   n_it->assertions.begin(); a_it != n_it->assertions.end(); a_it++) 
    {
      find_symbols(*a_it,symbols);
    }
    find_symbols(n_it->enabling_expr,symbols);
  }

  for(std::set<symbol_exprt>::const_iterator it = symbols.begin();
      it != symbols.end(); it++)
  {
    out << from_type(SSA.ns, "",it->type()) << " " << 
      from_expr(SSA.ns, "", *it) << ";\n";
  }
  out << "\n";
}

/*******************************************************************\

Function: show_value_set

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void show_value_set(
  const goto_functionst::goto_functiont &goto_function,
  const namespacet &ns,
  std::ostream &out)
{
  ssa_objectst ssa_objects(goto_function, ns);
  ssa_value_ait ssa_value_ai(goto_function, ns);
  ssa_value_ai.output(ns, goto_function, out);
}

/*******************************************************************\

Function: show_value_sets

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void show_value_sets(
  const goto_modelt &goto_model,
  const irep_idt &function,
  std::ostream &out,
  message_handlert &message_handler)
{
  const namespacet ns(goto_model.symbol_table);
  
  if(!function.empty())
  {
    goto_functionst::function_mapt::const_iterator
      f_it=goto_model.goto_functions.function_map.find(function);
    if(f_it==goto_model.goto_functions.function_map.end())
      out << "function " << function << " not found\n";
    else
      show_value_set(f_it->second, ns, out);
  }
  else
  {
    forall_goto_functions(f_it, goto_model.goto_functions)
    {
      out << ">>>> Function " << f_it->first << "\n";
          
      show_value_set(f_it->second, ns, out);
      
      out << "\n";
    }
  }
}

