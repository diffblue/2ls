/*******************************************************************\

Module: Showing various debugging information

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/options.h>

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
  ssa_value_ait ssa_value_ai;
  ssa_value_ai(goto_function, ns);
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
  ssa_value_ait ssa_value_ai;
  ssa_value_ai(goto_function, ns);
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
  local_SSA.output(out);
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
  ssa_value_ait ssa_value_ai;
  ssa_value_ai(goto_function, ns);
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

