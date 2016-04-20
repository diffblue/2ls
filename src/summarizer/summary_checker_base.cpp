/*******************************************************************\

Module: Summarizer Checker Base

Author: Peter Schrammel

\*******************************************************************/

#include <iostream>

#include <util/options.h>
#include <util/i2string.h>
#include <util/simplify_expr.h>
#include <langapi/language_util.h>
#include <util/prefix.h>
#include <goto-programs/write_goto_binary.h>

#include <solvers/sat/satcheck.h>
#include <solvers/flattening/bv_pointers.h>
#include <solvers/prop/literal_expr.h>

#include "../ssa/local_ssa.h"
#include "../ssa/simplify_ssa.h"
#include "../ssa/ssa_build_goto_trace.h"
#include "../domains/ssa_analyzer.h"
#include "../ssa/ssa_unwinder.h"
#include <cstdlib>

#include "show.h"
#include "instrument_goto.h"

#include "summary_checker_base.h"

#include "summarizer_fw.h"
#include "summarizer_fw_term.h"
#include "summarizer_bw.h"
#include "summarizer_bw_term.h"

#ifdef SHOW_CALLING_CONTEXTS
#include "summarizer_fw_contexts.h"
#endif

/*******************************************************************\

Function: summary_checker_baset::SSA_functions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summary_checker_baset::SSA_functions(const goto_modelt &goto_model,  const namespacet &ns)
{  
  // compute SSA for all the functions
  forall_goto_functions(f_it, goto_model.goto_functions)
  {
    if(!f_it->second.body_available()) continue;
    if(has_prefix(id2string(f_it->first),TEMPLATE_DECL)) continue;
    status() << "Computing SSA of " << f_it->first << messaget::eom;
    
    ssa_db.create(f_it->first, f_it->second, ns);
    local_SSAt &SSA = ssa_db.get(f_it->first);
    
    // simplify, if requested
    if(simplify)
    {
      status() << "Simplifying" << messaget::eom;
      ::simplify(SSA, ns);
    }

    SSA.output(debug()); debug() << eom;
  }

  // properties
  initialize_property_map(goto_model.goto_functions);
}

/*******************************************************************\

Function: summary_checker_baset::summarize

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summary_checker_baset::summarize(const goto_modelt &goto_model, 
				 bool forward,
				 bool termination)
{    
  summarizer_baset *summarizer = NULL;

#ifdef SHOW_CALLING_CONTEXTS
  if(options.get_bool_option("show-calling-contexts"))
    summarizer = new summarizer_fw_contextst(
      options,summary_db,ssa_db,ssa_unwinder,ssa_inliner);
  else
#endif
  {
  if(forward && !termination)
    summarizer = new summarizer_fwt(
      options,summary_db,ssa_db,ssa_unwinder,ssa_inliner);
  if(forward && termination)
    summarizer = new summarizer_fw_termt(
      options,summary_db,ssa_db,ssa_unwinder,ssa_inliner);
  if(!forward && !termination)
    summarizer = new summarizer_bwt(
      options,summary_db,ssa_db,ssa_unwinder,ssa_inliner);
  if(!forward && termination)
    summarizer = new summarizer_bw_termt(
      options,summary_db,ssa_db,ssa_unwinder,ssa_inliner);
  }
  assert(summarizer != NULL);

  summarizer->set_message_handler(get_message_handler());

  if(!options.get_bool_option("context-sensitive"))
    summarizer->summarize();
  else
    summarizer->summarize(goto_model.goto_functions.entry_point());

  //statistics
  solver_instances += summarizer->get_number_of_solver_instances();
  solver_calls += summarizer->get_number_of_solver_calls();
  summaries_used += summarizer->get_number_of_summaries_used();

  delete summarizer;
}
/*******************************************************************\

Function: summary_checker_baset::check_properties

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

summary_checker_baset::resultt summary_checker_baset::check_properties()
{
  // analyze all the functions
  for(ssa_dbt::functionst::const_iterator f_it = ssa_db.functions().begin();
      f_it != ssa_db.functions().end(); f_it++)
  {
    status() << "Checking properties of " << f_it->first << messaget::eom;

#if 0
    //for debugging
    show_ssa_symbols(*f_it->second,std::cerr);
#endif

    check_properties(f_it);

    if(options.get_bool_option("show-invariants")) 
    {
      if(!summary_db.exists(f_it->first)) continue;
      show_invariants(*(f_it->second),summary_db.get(f_it->first),result());
      result() << eom;
    }
  }
  
  summary_checker_baset::resultt result = property_checkert::PASS;
  for(property_mapt::const_iterator
      p_it=property_map.begin(); p_it!=property_map.end(); p_it++)
  {
    if(p_it->second.result==FAIL)
      return property_checkert::FAIL;
    if(p_it->second.result==UNKNOWN)
      result = property_checkert::UNKNOWN;
  }
    
  return result;
}

/*******************************************************************\

Function: summary_checker_baset::check_properties

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summary_checker_baset::check_properties(
   const ssa_dbt::functionst::const_iterator f_it)
{
  unwindable_local_SSAt &SSA = *f_it->second;
  
  bool all_properties = options.get_bool_option("all-properties");

  SSA.output_verbose(debug()); debug() << eom;
  
  // incremental version

  // solver
  incremental_solvert &solver = ssa_db.get_solver(f_it->first);
  solver.set_message_handler(get_message_handler());

  // give SSA to solver
  solver << SSA;
  SSA.mark_nodes();

  solver.new_context();

  exprt enabling_expr = SSA.get_enabling_exprs();
  solver << enabling_expr;

  // invariant, calling contexts
  if(summary_db.exists(f_it->first))
  {
    solver << summary_db.get(f_it->first).fw_invariant;
    solver << summary_db.get(f_it->first).fw_precondition;
  }

  //callee summaries
  solver << ssa_inliner.get_summaries(SSA);

  //freeze loop head selects
  exprt::operandst loophead_selects = 
    get_loophead_selects(f_it->first,SSA,*solver.solver);
  //check whether loops have been fully unwound
  exprt::operandst loop_continues = 
    get_loop_continues(f_it->first,SSA,*solver.solver);
  bool fully_unwound = 
    is_fully_unwound(loop_continues,loophead_selects,solver);
  status() << "Loops " << (fully_unwound ? "" : "not ") 
	   << "fully unwound" << eom;

  cover_goals_extt cover_goals(
    SSA,solver,loophead_selects,property_map,
    !fully_unwound && options.get_bool_option("spurious-check"),
    all_properties,
    options.get_bool_option("show-trace") ||
    options.get_option("graphml-cex")!="" ||
    options.get_option("json-cex")!="");

#if 0   
  debug() << "(C) " << from_expr(SSA.ns,"",enabling_expr) << eom;
#endif

  const goto_programt &goto_program=SSA.goto_function.body;

  for(goto_programt::instructionst::const_iterator
      i_it=goto_program.instructions.begin();
      i_it!=goto_program.instructions.end();
      i_it++)
  {
    if(!i_it->is_assert())
      continue;
  
    const source_locationt &location=i_it->source_location;  
    irep_idt property_id = location.get_property_id();
    
    if(i_it->guard.is_true())
    {
      property_map[property_id].result=PASS;
      continue;
    }

    //do not recheck properties that have already been decided
    if(property_map[property_id].result!=UNKNOWN) continue; 

    if(property_id=="") //TODO: some properties do not show up in initialize_property_map
      continue;     

    std::list<local_SSAt::nodest::const_iterator> assertion_nodes;
    SSA.find_nodes(i_it,assertion_nodes);

    unsigned property_counter = 0;
    for(std::list<local_SSAt::nodest::const_iterator>::const_iterator
	  n_it=assertion_nodes.begin();
        n_it!=assertion_nodes.end();
        n_it++)
    {
      for(local_SSAt::nodet::assertionst::const_iterator
	    a_it=(*n_it)->assertions.begin();
	  a_it!=(*n_it)->assertions.end();
	  a_it++, property_counter++)
      {
	exprt property=*a_it;

	if(simplify)
	  property=::simplify_expr(property, SSA.ns);

#if 0
	std::cout << "property: " << from_expr(SSA.ns, "", property) << std::endl;
#endif
 
	property_map[property_id].location = i_it;
	cover_goals.goal_map[property_id].conjuncts.push_back(property);
      }
    }
  }
    
  for(cover_goals_extt::goal_mapt::const_iterator
      it=cover_goals.goal_map.begin();
      it!=cover_goals.goal_map.end();
      it++)
  {
    // Our goal is to falsify a property.
    // The following is TRUE if the conjunction is empty.
    literalt p=!solver.convert(conjunction(it->second.conjuncts));
    cover_goals.add(p);
  }

  status() << "Running " << solver.solver->decision_procedure_text() << eom;

  cover_goals();  

  //set all non-covered goals to PASS except if we do not try 
  //  to cover all goals and we have found a FAIL
  if(all_properties || cover_goals.number_covered()==0) 
  {
    std::list<cover_goals_extt::cover_goalt>::const_iterator g_it=
      cover_goals.goals.begin();
    for(cover_goals_extt::goal_mapt::const_iterator
	  it=cover_goals.goal_map.begin();
	it!=cover_goals.goal_map.end();
	it++, g_it++)
    {
      if(!g_it->covered) property_map[it->first].result=PASS;
    }
  }

  solver.pop_context();

  debug() << "** " << cover_goals.number_covered()
           << " of " << cover_goals.size() << " failed ("
           << cover_goals.iterations() << " iterations)" << eom;
} 

/*******************************************************************\

Function: summary_checker_baset::report_statistics()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summary_checker_baset::report_statistics()
{
  for(ssa_dbt::functionst::const_iterator f_it = ssa_db.functions().begin();
	f_it != ssa_db.functions().end(); f_it++)
  {
    incremental_solvert &solver = ssa_db.get_solver(f_it->first);
    unsigned calls = solver.get_number_of_solver_calls();
    if(calls>0) solver_instances++;
    solver_calls += calls;
  }
  statistics() << "** statistics: " << eom;
  statistics() << "  number of solver instances: " << solver_instances << eom;
  statistics() << "  number of solver calls: " << solver_calls << eom;
  statistics() << "  number of summaries used: " 
               << summaries_used << eom;
  statistics() << eom;
}
  
/*******************************************************************\

Function: summary_checker_baset::do_show_vcc

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summary_checker_baset::do_show_vcc(
  const local_SSAt &SSA,
  const goto_programt::const_targett i_it,
  const local_SSAt::nodet::assertionst::const_iterator &a_it)
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
  
  std::cout << "{1} " << from_expr(SSA.ns, "", *a_it) << "\n";
  
  std::cout << "\n";
}

/*******************************************************************\

Function: summary_checker_baset::get_loophead_selects

  Inputs:

 Outputs:

 Purpose: returns the select guards at the loop heads 
          in order to check whether a countermodel is spurious

\*******************************************************************/

exprt::operandst summary_checker_baset::get_loophead_selects(
  const irep_idt &function_name, 
  const local_SSAt &SSA, prop_convt &solver)
{
  //TODO: this should be provided by unwindable_local_SSA
  exprt::operandst loophead_selects;
  for(local_SSAt::nodest::const_iterator n_it = SSA.nodes.begin();
      n_it != SSA.nodes.end(); n_it++)
  {
    if(n_it->loophead==SSA.nodes.end()) continue;
    symbol_exprt lsguard = SSA.name(SSA.guard_symbol(), local_SSAt::LOOP_SELECT, n_it->location);
    ssa_unwinder.get(function_name).unwinder_rename(lsguard,*n_it,true);
    loophead_selects.push_back(not_exprt(lsguard));
    solver.set_frozen(solver.convert(lsguard));
  }
  literalt loophead_selects_literal = solver.convert(conjunction(loophead_selects));
  if(!loophead_selects_literal.is_constant())
    solver.set_frozen(loophead_selects_literal);

#if 0
  std::cout << "loophead_selects: " << from_expr(SSA.ns,"",conjunction(loophead_selects)) << std::endl;
#endif

  return loophead_selects;
}

/*******************************************************************\

Function: summary_checker_baset::get_loop_continues

  Inputs:

 Outputs:

 Purpose: returns the loop continuation guards at the end of the
          loops in order to check whether we can unroll further

\*******************************************************************/

exprt::operandst summary_checker_baset::get_loop_continues(
  const irep_idt &function_name, 
  const local_SSAt &SSA, prop_convt &solver)
{
  //TODO: this should be provided by unwindable_local_SSA
  exprt::operandst loop_continues;

  ssa_unwinder.get(function_name).loop_continuation_conditions(loop_continues);
  if(loop_continues.size()==0) 
  {
    //TODO: this should actually be done transparently by the unwinder
    for(local_SSAt::nodest::const_iterator n_it = SSA.nodes.begin();
	n_it != SSA.nodes.end(); n_it++)
    {
      if(n_it->loophead==SSA.nodes.end()) continue;
      symbol_exprt guard = SSA.guard_symbol(n_it->location);
      symbol_exprt cond = SSA.cond_symbol(n_it->location);
      loop_continues.push_back(and_exprt(guard,cond));
    }
  }

#if 0
  std::cout << "loophead_continues: " << from_expr(SSA.ns,"",disjunction(loop_continues)) << std::endl;
#endif

  return loop_continues;
}

/*******************************************************************\

Function: summary_checker_baset::is_fully_unwound

  Inputs:

 Outputs:

 Purpose: checks whether the loops have been fully unwound

\*******************************************************************/

bool summary_checker_baset::is_fully_unwound(
  const exprt::operandst &loop_continues, 
  const exprt::operandst &loophead_selects,
  incremental_solvert &solver)
{
  solver.new_context();
  solver << and_exprt(conjunction(loophead_selects),
		      disjunction(loop_continues));

  solver_calls++; //statistics

  switch(solver())
  {
  case decision_proceduret::D_SATISFIABLE:
    solver.pop_context();
    return false;
    break;
      
  case decision_proceduret::D_UNSATISFIABLE:
    solver.pop_context();
    solver << conjunction(loophead_selects); 
    return true;
    break;

  case decision_proceduret::D_ERROR:    
  default:
    throw "error from decision procedure";
  }
}

/*******************************************************************\

Function: summary_checker_baset::is_spurious

  Inputs:

 Outputs:

 Purpose: checks whether a countermodel is spurious

\*******************************************************************/

bool summary_checker_baset::is_spurious(const exprt::operandst &loophead_selects, 
				   incremental_solvert &solver)
{
  //check loop head choices in model
  bool invariants_involved = false;
  for(exprt::operandst::const_iterator l_it = loophead_selects.begin();
        l_it != loophead_selects.end(); l_it++)
  {
    if(solver.get(l_it->op0()).is_true()) 
    {
      invariants_involved = true; 
      break;
    }
  }
  if(!invariants_involved) return false;
  
  // force avoiding paths going through invariants
  solver << conjunction(loophead_selects);

  solver_calls++; //statistics

  switch(solver())
  {
  case decision_proceduret::D_SATISFIABLE:
    return false;
    break;
      
  case decision_proceduret::D_UNSATISFIABLE:
    return true;
    break;

  case decision_proceduret::D_ERROR:    
  default:
    throw "error from decision procedure";
  }
}

/*******************************************************************\

Function: summary_checker_baset::instrument_and_output

  Inputs:

 Outputs:

 Purpose: instruments the code with the inferred information
          and outputs it to a goto-binary

\*******************************************************************/

void summary_checker_baset::instrument_and_output(goto_modelt &goto_model)
{
  instrument_gotot instrument_goto(options,ssa_db,summary_db);
  instrument_goto(goto_model);
  std::string filename = options.get_option("instrument-output");
  status() << "Writing instrumented goto-binary " << filename << eom;
  write_goto_binary(filename, 
		    goto_model.symbol_table, 
		    goto_model.goto_functions, get_message_handler());
}
