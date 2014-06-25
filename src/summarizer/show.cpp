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
  assignmentst assignments(goto_function.body, ns, ssa_objects);
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
  std::ostream &out,
  message_handlert &message_handler)
{
  const namespacet ns(goto_model.symbol_table);
  
  forall_goto_functions(f_it, goto_model.goto_functions)
  {
    out << ">>>> Function " << f_it->first << "\n";
          
    show_assignments(f_it->second, ns, out);
      
    out << "\n";
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
  assignmentst assignments(goto_function.body, ns, ssa_objects);
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
  std::ostream &out,
  message_handlert &message_handler)
{
  const namespacet ns(goto_model.symbol_table);
  
  forall_goto_functions(f_it, goto_model.goto_functions)
  {
    out << ">>>> Function " << f_it->first << "\n";
          
    show_defs(f_it->second, ns, out);
      
    out << "\n";
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
  std::ostream &out,
  message_handlert &message_handler)
{
  const namespacet ns(goto_model.symbol_table);
  
  forall_goto_functions(f_it, goto_model.goto_functions)
  {
    out << ">>>> Function " << f_it->first << "\n";
          
    show_guards(f_it->second, ns, out);
      
    out << "\n";
  }
}

/*******************************************************************\

Function: show_ssa

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

#include "../ssa/ssa_unwinder.h"

void show_ssa(
  const goto_functionst::goto_functiont &goto_function,
  bool simplify,
  const namespacet &ns,
  std::ostream &out)
{
  local_SSAt local_SSA(goto_function, ns);
  local_SSA.assertions_to_constraints();
  if(simplify) ::simplify(local_SSA, ns);

#if 0
  ssa_unwindert ssa_unwinder;
  ssa_unwinder.unwind(local_SSA,1);
#endif

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
  bool simplify,
  std::ostream &out,
  message_handlert &message_handler)
{
  const namespacet ns(goto_model.symbol_table);
  
  forall_goto_functions(f_it, goto_model.goto_functions)
  {
    if(f_it->first=="c::assert") continue;
    if(f_it->first=="c::__CPROVER_assume") continue;
  
    out << ">>>> Function " << f_it->first << "\n";
          
    show_ssa(f_it->second, simplify, ns, out);
      
    out << "\n";
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
  bool simplify,
  std::ostream &out,
  message_handlert &message_handler)
{
  const namespacet ns(goto_model.symbol_table);
  
  forall_goto_functions(f_it, goto_model.goto_functions)
  {
    out << ">>>> Function " << f_it->first << "\n";
          
    show_fixed_point(f_it->second, simplify, ns, out);
      
    out << "\n";
  }
}

