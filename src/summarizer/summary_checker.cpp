/*******************************************************************\

Module: Summarizer

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iostream>

#include <util/options.h>
#include <util/simplify_expr.h>
#include <langapi/language_util.h>

#include <solvers/sat/satcheck.h>
#include <solvers/flattening/bv_pointers.h>

#include "../ssa/local_ssa.h"
#include "../ssa/simplify_ssa.h"
#include "../ssa/ssa_build_goto_trace.h"
#include "../domains/ssa_fixed_point.h"
#include "../domains/ssa_analyzer.h"

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
  const namespacet ns(goto_model.symbol_table);
  SSA_functions(goto_model,ns);
  summarize();
  return check_properties(); 
  // return check_properties(goto_model);
}

/*******************************************************************\

Function: summary_checkert::SSA_functions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summary_checkert::SSA_functions(const goto_modelt &goto_model,  const namespacet &ns)
{
  // properties
  initialize_property_map(goto_model.goto_functions);
  
  // compute SSA for all the functions
  forall_goto_functions(f_it, goto_model.goto_functions)
  {
    if(!f_it->second.body_available) continue;

    status() << "Computing SSA of " << f_it->first << messaget::eom;
    
    local_SSAt *SSA = new local_SSAt(f_it->second, ns);
    
    // simplify, if requested
    if(simplify)
    {
      status() << "Simplifying" << messaget::eom;
      ::simplify(*SSA, ns);
    }

    SSA->output(debug()); debug() << eom;
    functions[f_it->first] = SSA;
  }

#if 0
  // inline c::main and __CPROVER_initialize
  ssa_inlinert ssa_inliner;
  ssa_inliner.set_message_handler(get_message_handler());
  ssa_inliner.set_verbosity(get_verbosity());     

  ssa_inliner.replace(*functions[ID_main],functions,false,false);
  
  functions[ID_main]->output(debug()); debug() << eom;
#endif
}

/*******************************************************************\

Function: summary_checkert::summarize

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summary_checkert::summarize()
{    
  summarizer.set_message_handler(get_message_handler());
  summarizer.set_verbosity(get_verbosity());

  summarizer.summarize(functions);
}

/*******************************************************************\

Function: summary_checkert::check_properties

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

summary_checkert::resultt summary_checkert::check_properties()
{
  // analyze all the functions
  for(summarizert::functionst::const_iterator f_it = functions.begin();
      f_it != functions.end(); f_it++)
  {
    status() << "Checking properties of " << f_it->first << messaget::eom;
    check_properties(f_it);
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
   const summarizert::functionst::const_iterator f_it)
{
  const local_SSAt &SSA = *f_it->second;
  if(!SSA.goto_function.body.has_assertion()) return;

  SSA.output(debug()); debug() << eom;
  
  // non-incremental version

  const goto_programt &goto_program=SSA.goto_function.body;

  for(goto_programt::instructionst::const_iterator
      i_it=goto_program.instructions.begin();
      i_it!=goto_program.instructions.end();
      i_it++)
  {
    if(!i_it->is_assert())
      continue;
  
    const locationt &location=i_it->location;  
    irep_idt property_id=location.get_property_id();

    if(show_vcc)
    {
      do_show_vcc(SSA, i_it);
      continue;
    }
  
    // solver
    satcheckt satcheck;
    bv_pointerst solver(SSA.ns, satcheck);
  
    satcheck.set_message_handler(get_message_handler());
    solver.set_message_handler(get_message_handler());
    
    // give SSA to solver
    solver << SSA;

    // give negation of property to solver

    exprt negated_property=SSA.read_rhs(not_exprt(i_it->guard), i_it);

    if(simplify)
      negated_property=::simplify_expr(negated_property, SSA.ns);
  
    solver << SSA.guard_symbol(i_it);    
    
    std::cout << "negated property " << from_expr(SSA.ns, "", negated_property) << std::endl;
    
          
    solver << negated_property;
    
    // solve
    switch(solver())
    {
    case decision_proceduret::D_SATISFIABLE:
      property_map[property_id].result=FAIL;
      break;
      
    case decision_proceduret::D_UNSATISFIABLE:
      property_map[property_id].result=PASS;
      break;

    case decision_proceduret::D_ERROR:    
    default:
      property_map[property_id].result=ERROR;
      throw "error from decision procedure";
    }
  }
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
    if(!f_it->second.body_available) continue;

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
    ssa_analyzert ssa_analyzer(ns, options);
    ssa_analyzer(SSA);

    // Add fixed-point as constraints back into SSA.
    // We simply use the last CFG node. It would be prettier to put
    // these close to the loops.
    goto_programt::const_targett loc=
      SSA.goto_function.body.instructions.end();
    loc--;
    local_SSAt::nodet &node=SSA.nodes[loc];
    exprt inv;
    ssa_analyzer.get_loop_invariants(inv);
    node.constraints.push_back(inv);
    //ssa_fixed_point(SSA);

    status() << "Checking properties" << messaget::eom;
    check_properties(SSA, f_it);
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

#include "../ssa/ssa_domain.h"

void summary_checkert::check_properties(
  const local_SSAt &SSA0,
  const goto_functionst::function_mapt::const_iterator f_it)
{
  local_SSAt SSA = SSA0;
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
  
  // inline summaries
  summarizer.inline_summaries(f_it->first,SSA.nodes);
  
  #if 0
  // simplify, if requested
  if(simplify)
  {
    status() << "Simplifying" <<messaget::eom;
    ::simplify(SSA, ns);
  }
  #endif

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
    irep_idt property_id=location.get_property_id();

    if(show_vcc)
    {
      do_show_vcc(SSA, i_it);
      continue;
    }
  
    // solver
    satcheckt satcheck;
    bv_pointerst solver(SSA.ns, satcheck);
  
    satcheck.set_message_handler(get_message_handler());
    solver.set_message_handler(get_message_handler());
    
    // give SSA to solver
    solver << SSA;

    // give negation of property to solver

    exprt negated_property=SSA.read_rhs(not_exprt(i_it->guard), i_it);

    if(simplify)
      negated_property=::simplify_expr(negated_property, SSA.ns);
  
    solver << SSA.guard_symbol(i_it);          
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
  std::cout << i_it->location << "\n";
  std::cout << i_it->location.get_comment() << "\n";
  
  std::list<exprt> ssa_constraints;
  ssa_constraints << SSA;

  unsigned i=1;
  for(std::list<exprt>::const_iterator c_it=ssa_constraints.begin();
      c_it!=ssa_constraints.end();
      c_it++, i++)
    std::cout << "{-" << i << "} " << from_expr(SSA.ns, "", *c_it) << "\n";

  std::cout << "|--------------------------\n";
  
  exprt property_rhs=SSA.read_rhs(i_it->guard, i_it);
  
  if(simplify)
    property_rhs=::simplify_expr(property_rhs, SSA.ns);
  
  implies_exprt property(
    SSA.guard_symbol(i_it), property_rhs);

  std::cout << "{1} " << from_expr(SSA.ns, "", property) << "\n";
  
  std::cout << "\n";
}

