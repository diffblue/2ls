/*******************************************************************\

Module: Summarizer

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iostream>

#include <util/simplify_expr.h>
#include <langapi/language_util.h>

#include <solvers/sat/satcheck.h>
#include <solvers/flattening/bv_pointers.h>

#include "../ssa/local_ssa.h"
#include "../ssa/simplify_ssa.h"

#include "summary_checker.h"

/*******************************************************************\

Function: summary_checkert::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

summary_checkert::resultt summary_checkert::operator()(
  const goto_functionst &goto_functions)
{
  return check_properties(goto_functions);
}

/*******************************************************************\

Function: summary_checkert::check_properties

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

summary_checkert::resultt summary_checkert::check_properties(
  const goto_functionst &goto_functions)
{
  // properties
  initialize_property_map(goto_functions);

  // compute summaries for all the functions
  summarizert::functionst functions;
  forall_goto_functions(f_it, goto_functions)
  {
    if(f_it->first=="c::assert") continue;
    if(f_it->first=="c::__CPROVER_assume") continue;
    functions[f_it->first] = new local_SSAt(f_it->second, ns);
  }
  summarizer.summarize(functions);

  // analyze all the functions
  forall_goto_functions(f_it, goto_functions)
    check_properties(f_it);
  
  for(property_mapt::const_iterator
      p_it=property_map.begin(); p_it!=property_map.end(); p_it++)
    if(p_it->second.status==FAIL)
      return safety_checkert::UNSAFE;
    
  return safety_checkert::SAFE;
}

/*******************************************************************\

Function: summary_checkert::check_properties

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

#include "../ssa/ssa_domain.h"

#include "../ai/ssa_cfg.h"

void summary_checkert::check_properties(
  const goto_functionst::function_mapt::const_iterator f_it)
{
  if(!f_it->second.body.has_assertion()) return;

  #if 0
  assignmentst assignments(f_it->second.body, ns);
  //assignments.output(ns, f_it->second.body, std::cout);
  
  ssa_ait ssa_ai(assignments);
  ssa_ai(f_it->second.body, ns);
  ssa_ai.output(ns, f_it->second.body, std::cout);
  return;
  #endif
  
  status() << "Analyzing " << f_it->first << messaget::eom;
  
  // build SSA
  local_SSAt SSA(f_it->second, ns);

  //ssa_cfgt ssa_cfg(SSA);

  // inline summaries
  summarizer.inline_summaries(SSA.nodes);
  
  // simplify, if requested
  if(simplify)
  {
    status() << "Simplifying" <<messaget::eom;
    ::simplify(SSA, ns);
  }

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

    if(show_vcc)
    {
      do_show_vcc(SSA, i_it);
      continue;
    }
  
    // solver
    satcheckt satcheck;
    bv_pointerst solver(ns, satcheck);
  
    satcheck.set_message_handler(get_message_handler());
    solver.set_message_handler(get_message_handler());
    
    // give SSA to solver
    solver << SSA;

    // give negation of property to solver

    exprt negated_property=SSA.read_rhs(not_exprt(i_it->guard), i_it);

    if(simplify)
      negated_property=::simplify_expr(negated_property, ns);
  
    solver << SSA.guard_symbol(i_it);          
    solver << negated_property;
    
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
  std::cout << i_it->location << "\n";
  std::cout << i_it->location.get_comment() << "\n";
  
  std::list<exprt> ssa_constraints;
  ssa_constraints << SSA;

  unsigned i=1;
  for(std::list<exprt>::const_iterator c_it=ssa_constraints.begin();
      c_it!=ssa_constraints.end();
      c_it++, i++)
    std::cout << "{-" << i << "} " << from_expr(ns, "", *c_it) << "\n";

  std::cout << "|--------------------------\n";
  
  exprt property_rhs=SSA.read_rhs(i_it->guard, i_it);
  
  if(simplify)
    property_rhs=::simplify_expr(property_rhs, ns);
  
  implies_exprt property(
    SSA.guard_symbol(i_it), property_rhs);

  std::cout << "{1} " << from_expr(ns, "", property) << "\n";
  
  std::cout << "\n";
}

/*******************************************************************\

Function: summary_checkert::initialize_property_map

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summary_checkert::initialize_property_map(
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
