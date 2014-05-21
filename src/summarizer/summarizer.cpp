/*******************************************************************\

Module: Summarizer

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <solvers/sat/satcheck.h>
#include <solvers/flattening/bv_pointers.h>

#include "../ssa/local_ssa.h"

#include "summarizer.h"

/*******************************************************************\

Function: summarizert::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

summarizert::resultt summarizert::operator()(
  const goto_functionst &goto_functions)
{
  // get the entry point
  const goto_functionst::function_mapt::const_iterator
    f_it=goto_functions.function_map.find(goto_functions.entry_point());
    
  if(f_it==goto_functions.function_map.end())
    throw "Failed to find entry point, please complete linking.";

  // properties
  
  initialize_property_map(goto_functions);

  // analyze entry function
  
  analyze(f_it);
  
  for(property_mapt::const_iterator
      p_it=property_map.begin(); p_it!=property_map.end(); p_it++)
    if(p_it->second.status==FAIL)
      return safety_checkert::UNSAFE;
    
  return safety_checkert::SAFE;
}

/*******************************************************************\

Function: summarizert::analyze

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarizert::analyze(
  const goto_functionst::function_mapt::const_iterator f_it)
{
  // build SSA
  local_SSAt SSA(f_it->second, ns);

  // non-incremental version

  const goto_programt &goto_program=f_it->second.body;

  for(goto_programt::instructionst::const_iterator
      i_it=goto_program.instructions.begin();
      i_it!=goto_program.instructions.end();
      i_it++)
  {
    if(!i_it->is_assert())
      continue;
  
    const locationt &location=i_it->location;  
    irep_idt property_name=location.get_property_id();

    // solver
    satcheckt satcheck;
    bv_pointerst solver(ns, satcheck);
  
    satcheck.set_message_handler(get_message_handler());
    solver.set_message_handler(get_message_handler());
  
    // give SSA to solver
    solver << SSA;

    // give property to solver
    solver << SSA.guard_symbol(i_it);          
    solver << SSA.read_rhs(i_it->guard, i_it);
    
    // solve
    switch(solver())
    {
    case decision_proceduret::D_SATISFIABLE:
      property_map[property_name].status=FAIL;
      break;
      
    case decision_proceduret::D_UNSATISFIABLE:
      property_map[property_name].status=PASS;
      break;

    case decision_proceduret::D_ERROR:    
    default:
      throw "error from decision procedure";
    }
  }
} 
  
/*******************************************************************\

Function: summarizert::report_statistics()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarizert::report_statistics()
{
}
  
/*******************************************************************\

Function: summarizert::initialize_property_map

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarizert::initialize_property_map(
  const goto_functionst &goto_functions)
{
  for(goto_functionst::function_mapt::const_iterator
      it=goto_functions.function_map.begin();
      it!=goto_functions.function_map.end();
      it++)
    if(!it->second.is_inlined() ||
       it->first==goto_functions.entry_point())
    {
      const goto_programt &goto_program=it->second.body;
    
      for(goto_programt::instructionst::const_iterator
          it=goto_program.instructions.begin();
          it!=goto_program.instructions.end();
          it++)
      {
        if(!it->is_assert())
          continue;
      
        const locationt &location=it->location;
      
        irep_idt property_name=location.get_property_id();
        
        property_entryt &property_entry=property_map[property_name];
        property_entry.status=UNKNOWN;
        property_entry.description=location.get_comment();
      }
    }
}
