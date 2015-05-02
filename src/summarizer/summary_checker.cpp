/*******************************************************************\

Module: Summary Checker

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iostream>

#include <util/simplify_expr.h>
#include <langapi/language_util.h>

#include <solvers/sat/satcheck.h>
#include <solvers/flattening/bv_pointers.h>

#include "../ssa/local_ssa.h"
#include "../ssa/simplify_ssa.h"
#include "../ssa/ssa_build_goto_trace.h"
#include "../domains/ssa_fixed_point.h"

#include "summary_checker.h"

/*******************************************************************\

Function: summary_checkert::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

property_checkert::resultt summary_checkert::operator()(
  const goto_modelt &goto_model)
{
  return check_properties(goto_model);
}

/*******************************************************************\

Function: summary_checkert::check_properties

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

summary_checkert::resultt summary_checkert::check_properties(
  const goto_modelt &goto_model)
{
  // properties
  initialize_property_map(goto_model.goto_functions);
  
  const namespacet ns(goto_model.symbol_table);

  // analyze all the functions
  forall_goto_functions(f_it, goto_model.goto_functions)
  {
    if(!f_it->second.body.has_assertion()) continue;
    check_properties(f_it, ns);
  }
  
  for(property_mapt::const_iterator
      p_it=property_map.begin(); p_it!=property_map.end(); p_it++)
    if(p_it->second.result==FAIL)
      return property_checkert::FAIL;
    
  return property_checkert::PASS;
}

/*******************************************************************\

Function: summary_checkert::check_properties

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summary_checkert::check_properties(
  const goto_functionst::function_mapt::const_iterator f_it,
  const namespacet &ns)
{
  status() << "Analyzing " << f_it->first << messaget::eom;
  
  // build SSA
  local_SSAt SSA(f_it->second, ns);
  
  // simplify, if requested
  if(simplify)
  {
    status() << "Simplifying" << messaget::eom;
    ::simplify(SSA, ns);
  }
  
  // fixed-point for loops
  status() << "Fixed-point" << messaget::eom;
  ssa_fixed_point(SSA);

  status() << "Checking properties" << messaget::eom;

  const goto_programt &goto_program=f_it->second.body;

  for(goto_programt::instructionst::const_iterator
      i_it=goto_program.instructions.begin();
      i_it!=goto_program.instructions.end();
      i_it++)
  {
    if(!i_it->is_assert())
      continue;
  
    const source_locationt &source_location=i_it->source_location;  
    irep_idt property_id=source_location.get_property_id();

    if(show_vcc)
    {
      do_show_vcc(SSA, i_it);
      continue;
    }
  
    // solver
    satcheckt satcheck;
    bv_pointerst solver(SSA.ns, satcheck);
    solver.unbounded_array=bv_pointerst::U_AUTO;
  
    satcheck.set_message_handler(get_message_handler());
    solver.set_message_handler(get_message_handler());
    
    // give SSA to solver
    solver << SSA;

    // give negation of property to solver
    exprt negated_property=not_exprt(SSA.assertion(i_it));

    solver << negated_property;
    
    property_statust &property_status=property_map[property_id];
    
    // solve
    switch(solver())
    {
    case decision_proceduret::D_SATISFIABLE:
      property_status.result=FAIL;
      build_goto_trace(SSA, solver, property_status.error_trace);
      break;
      
    case decision_proceduret::D_UNSATISFIABLE:
      property_status.result=PASS;
      break;

    case decision_proceduret::D_ERROR:    
    default:
      property_status.result=ERROR;
      throw "error from decision procedure";
    }
  }
} 
  
/*******************************************************************\

Function: summary_checkert::report_statistics()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summary_checkert::report_statistics()
{
}
  
/*******************************************************************\

Function: summary_checkert::do_show_vcc

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summary_checkert::do_show_vcc(
  const local_SSAt &SSA,
  const goto_programt::const_targett i_it)
{
  std::cout << i_it->source_location << "\n";
  std::cout << i_it->source_location.get_comment() << "\n";
  
  std::list<exprt> ssa_constraints;
  ssa_constraints << SSA;

  unsigned i=1;
  for(std::list<exprt>::const_iterator c_it=ssa_constraints.begin();
      c_it!=ssa_constraints.end();
      c_it++, i++)
    std::cout << "{-" << i << "} " << from_expr(SSA.ns, "", *c_it) << "\n";

  std::cout << "|--------------------------\n";
  
  exprt property=SSA.assertion(i_it);
  
  std::cout << "{1} " << from_expr(SSA.ns, "", property) << "\n";
  
  std::cout << "\n";
}

