/*******************************************************************\

Module: Summarizer

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iostream>

#include <util/options.h>
#include <util/i2string.h>
#include <util/simplify_expr.h>
#include <langapi/language_util.h>

#include <solvers/sat/satcheck.h>
#include <solvers/flattening/bv_pointers.h>
#include <solvers/prop/cover_goals.h>
#include <solvers/prop/literal_expr.h>

#include "../ssa/local_ssa.h"
#include "../ssa/simplify_ssa.h"
#include "../ssa/ssa_build_goto_trace.h"
#include "../domains/ssa_analyzer.h"
#include "../ssa/ssa_unwinder.h"
#include <cstdlib>


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
  bool preconditions = options.get_bool_option("preconditions");

  SSA_functions(goto_model,ns);
  //loop
  //  refine domain
  //  loop from 0 to k do
  //    unwind k

  if(!options.get_bool_option("havoc")) 
    summarize(goto_model,!preconditions,options.get_bool_option("sufficient"));

  if(preconditions) 
  {
    report_preconditions();
    return property_checkert::UNKNOWN;
  }

  property_checkert::resultt result =  check_properties(); 
  report_statistics();
  return result;
  //    if safe exit
  //  done
  //done
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
    
    ssa_db.create(f_it->first, f_it->second, ns);
    local_SSAt &SSA = ssa_db.get(f_it->first);
    
    // simplify, if requested
    if(simplify)
    {
      status() << "Simplifying" << messaget::eom;
      ::simplify(SSA, ns);
    }
  }
    unsigned unwind = options.get_unsigned_int_option("unwind");
    if(unwind>0)
    {
      status() << "Unwinding" << messaget::eom;


        ssa_unwinder.init();
    	  ssa_unwinder.unwind_all(unwind);
    	  ssa_unwinder.output(debug()); debug() <<eom;



    }




#if 0
  // inline c::main and __CPROVER_initialize
  ssa_inlinert ssa_inliner;
  ssa_inliner.set_message_handler(get_message_handler());

  ssa_inliner.replace(ssa_db.get(ID_main),functions,false,false);
  
  ssa_db.get(ID_main).output(debug()); debug() << eom;
#endif
}

/*******************************************************************\

Function: summary_checkert::summarize

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summary_checkert::summarize(const goto_modelt &goto_model, 
				 bool backward, bool sufficient)
{    
  summarizer.set_message_handler(get_message_handler());

  if(options.get_bool_option("context-sensitive"))
    summarizer.summarize(ssa_db.functions(),
			 goto_model.goto_functions.entry_point(),
                         backward,sufficient);
  else
    summarizer.summarize(ssa_db.functions(),backward,sufficient);

  //statistics
  solver_instances += summarizer.get_number_of_solver_instances();
  solver_calls += summarizer.get_number_of_solver_calls();
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
  for(summarizert::functionst::const_iterator f_it = ssa_db.functions().begin();
      f_it != ssa_db.functions().end(); f_it++)
  {
    status() << "Checking properties of " << f_it->first << messaget::eom;
    if(options.get_bool_option("incremental"))
      check_properties_incremental(f_it);
    else
      check_properties_non_incremental(f_it);
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

void summary_checkert::check_properties_non_incremental(
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
  
    const source_locationt &source_location=i_it->source_location;  
    const local_SSAt::nodet &node = *SSA.find_node(i_it);

    irep_idt property_id=source_location.get_property_id();

    if(property_id=="") //TODO: some properties do not show up in initialize_property_map
      continue;     

    property_map[property_id].location = i_it;
    
    exprt::operandst conjuncts;
    for(local_SSAt::nodet::assertionst::const_iterator
	  a_it=node.assertions.begin();
        a_it!=node.assertions.end();
        a_it++)
    {
      conjuncts.push_back(*a_it);

      if(show_vcc)
      {
        do_show_vcc(SSA, i_it, a_it);
        continue;
      }
    }
    exprt property = not_exprt(conjunction(conjuncts));
    if(simplify)
      property=::simplify_expr(property, SSA.ns);
  
    // solver
    satcheckt satcheck;
    bv_pointerst solver(SSA.ns, satcheck);
 
    satcheck.set_message_handler(get_message_handler());
    solver.set_message_handler(get_message_handler());
    
    // give SSA to solver
    solver << SSA;

    // give negated property to solver
    solver << property;

#if 0   
    //for future incremental usagae 
    solver->set_assumptions(
      strategy_solver_baset::convert_enabling_exprs(solver,SSA.enabling_exprs));
#endif
    solver << strategy_solver_baset::make_enabling_exprs(SSA.enabling_exprs);

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

    //statistics
    solver_instances++;
    solver_calls ++;;
  }
} 

/*******************************************************************\

Function: summary_checkert::check_properties

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

struct goalt
{
  // a property holds if all instances of it are true
  exprt::operandst conjuncts;
  std::string description;

  explicit goalt(const goto_programt::instructiont &instruction)
  {
    description=id2string(instruction.source_location.get_comment());
  }
  
  goalt()
  {
  }
};

/*******************************************************************\

Function: summary_checkert::check_properties_incremental

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summary_checkert::check_properties_incremental(
   const summarizert::functionst::const_iterator f_it)
{
  const local_SSAt &SSA = *f_it->second;
  if(!SSA.goto_function.body.has_assertion()) return;

  SSA.output(debug()); debug() << eom;
  
  // incremental version

  // solver
  satcheckt satcheck;
  bv_pointerst solver(SSA.ns, satcheck);
  
  satcheck.set_message_handler(get_message_handler());
  solver.set_message_handler(get_message_handler());
    
  // give SSA to solver
  solver << SSA;

#if 0   
    //for future incremental usagae 
    solver->set_assumptions(
      strategy_solver_baset::convert_enabling_exprs(solver,SSA.enabling_exprs));
#endif
    solver << strategy_solver_baset::make_enabling_exprs(SSA.enabling_exprs);

  // Collect _all_ goals in `goal_map'.
  // This maps claim IDs to 'goalt'
  typedef std::map<irep_idt, goalt> goal_mapt;
  goal_mapt goal_map;

  const goto_programt &goto_program=SSA.goto_function.body;

  for(goto_programt::instructionst::const_iterator
      i_it=goto_program.instructions.begin();
      i_it!=goto_program.instructions.end();
      i_it++)
  {
    if(!i_it->is_assert())
      continue;
  
    const locationt &location=i_it->source_location;  
    const local_SSAt::nodet &node = *SSA.find_node(i_it);

    irep_idt property_id = location.get_property_id();

    if(property_id=="") //TODO: some properties do not show up in initialize_property_map
      continue;     

    unsigned property_counter = 0;
    for(local_SSAt::nodet::assertionst::const_iterator
	  a_it=node.assertions.begin();
        a_it!=node.assertions.end();
        a_it++, property_counter++)
    {
      exprt property=*a_it;

      if(simplify)
	property=::simplify_expr(property, SSA.ns);

#if 0 
      std::cout << "property: " << from_expr(SSA.ns, "", property) << std::endl;
#endif
 
      property_map[property_id].location = i_it;
      goal_map[property_id].conjuncts.push_back(property);
    }
  }
  
  cover_goalst cover_goals(solver);
  
  for(goal_mapt::const_iterator
      it=goal_map.begin();
      it!=goal_map.end();
      it++)
  {
    // Our goal is to falsify a property.
    // The following is TRUE if the conjunction is empty.
    literalt p=!solver.convert(conjunction(it->second.conjuncts));
    cover_goals.add(p);
  }

  status() << "Running " << solver.decision_procedure_text() << eom;

  cover_goals();  

  std::list<cover_goalst::cover_goalt>::const_iterator g_it=
    cover_goals.goals.begin();
  for(goal_mapt::const_iterator
      it=goal_map.begin();
      it!=goal_map.end();
      it++, g_it++)
  {
    property_map[it->first].result=g_it->covered?FAIL:PASS;
  }

  //statistics
  solver_instances++;
  solver_calls += cover_goals.iterations();

  debug() << "** " << cover_goals.number_covered()
           << " of " << cover_goals.size() << " failed ("
           << cover_goals.iterations() << " iterations)" << eom;
} 

/*******************************************************************\

Function: summary_checkert::report_statistics()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summary_checkert::report_statistics()
{
  statistics() << "** statistics: " << eom;
  statistics() << "  number of solver instances: " << solver_instances << eom;
  statistics() << "  number of solver calls: " << solver_calls << eom;
  statistics() << "  number of summaries used: " 
               << summarizer.get_number_of_summaries_used() << eom;
  statistics() << eom;
}
  
/*******************************************************************\

Function: summary_checkert::do_show_vcc

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summary_checkert::do_show_vcc(
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

Function: summary_checkert::report_preconditions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summary_checkert::report_preconditions()
{
  bool sufficient = options.get_bool_option("sufficient");
  result() << eom;
  result() << "** Preconditions: " << eom;
  summarizert::functionst &functions = ssa_db.functions();
  for(summarizert::functionst::iterator it = functions.begin();
      it != functions.end(); it++)
  {
    exprt precondition = summary_db.get(it->first).precondition;
    if(sufficient) precondition = not_exprt(precondition);
    result() << eom << "[" << it->first << "]: " 
	     << from_expr(it->second->ns, "", precondition) << eom;
  }
}
