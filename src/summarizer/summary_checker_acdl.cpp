/*******************************************************************\

Module: Summary Checker using ACDL

Author: Peter Schrammel

\*******************************************************************/

#include <memory>

#include <util/simplify_expr.h>

#include "summary_checker_acdl.h"

#include "../acdl/acdl_solver.h"
#include "../acdl/acdl_domain.h"
#include "../acdl/acdl_decision_heuristics_base.h"
#include "../acdl/acdl_decision_heuristics_rand.h"
#include "../acdl/acdl_decision_heuristics_ordered.h"
#include "../acdl/acdl_decision_heuristics_octagon.h"
#include "../acdl/acdl_decision_heuristics_berkmin.h"
#include "../acdl/acdl_decision_heuristics_largest_range.h"
#include "../acdl/acdl_worklist_base.h"
#include "../acdl/acdl_worklist_ordered.h"
#include "../acdl/acdl_worklist_forward_strategy.h"
#include "../acdl/acdl_analyze_conflict_base.h"
//#include "../acdl/acdl_conflict_analysis_firstuip.h"

/*******************************************************************\

Function: summary_checker_acdlt::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

property_checkert::resultt summary_checker_acdlt::operator()(
  const goto_modelt &goto_model)
{
  const namespacet ns(goto_model.symbol_table);

  SSA_functions(goto_model,ns);
  ssa_unwinder.init(false,false);

  unsigned unwind = options.get_unsigned_int_option("unwind");
  if(unwind>0)
  {
    status() << "Unwinding" << messaget::eom;
    ssa_unwinder.init_localunwinders();
    ssa_unwinder.unwind_all(unwind);
  }

  irep_idt entry_point = goto_model.goto_functions.entry_point();
  std::cout << entry_point << std::endl;
  local_SSAt &SSA = ssa_db.get(entry_point);
  ssa_local_unwindert &ssa_local_unwinder = ssa_unwinder.get(entry_point);

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

    if(property_id=="") //TODO: some properties do not show up in initialize_property_map
      continue;     

    //get loophead selects
    exprt::operandst loophead_selects;
    for(local_SSAt::nodest::const_iterator n_it = SSA.nodes.begin();
	n_it != SSA.nodes.end(); n_it++)
    {
      if(n_it->loophead==SSA.nodes.end()) continue;
      symbol_exprt lsguard = SSA.name(SSA.guard_symbol(),
				      local_SSAt::LOOP_SELECT, n_it->location);
      ssa_unwinder.get(entry_point).unwinder_rename(lsguard,*n_it,true);
      loophead_selects.push_back(not_exprt(lsguard));
    }

    // iterate over assertions
    std::list<local_SSAt::nodest::const_iterator> assertion_nodes;
    SSA.find_nodes(i_it,assertion_nodes);
    std::cout << "The number of assertions are: " << assertion_nodes.size() << std::endl;
    exprt::operandst assertions;
    for(std::list<local_SSAt::nodest::const_iterator>::const_iterator
        n_it=assertion_nodes.begin();
        n_it!=assertion_nodes.end();
        n_it++)
    {
      for(local_SSAt::nodet::assertionst::const_iterator
          a_it=(*n_it)->assertions.begin();
          a_it!=(*n_it)->assertions.end();
          a_it++)
      {
        assertions.push_back(*a_it);
      }
    }
    //   if(simplify) property=simplify_expr(property, SSA.ns);
    property_map[property_id].location = i_it;

    //TODO: make the solver incremental

    // configure components of acdl solver
    // domain
    acdl_domaint domain(options,SSA,ssa_db,ssa_local_unwinder);
    domain.set_message_handler(get_message_handler());
    /*std::unique_ptr<acdl_worklist_baset> worklist =
      std::unique_ptr<acdl_worklist_baset>(new acdl_worklist_orderedt()); 
    std::unique_ptr<acdl_worklist_baset> worklist =
      std::unique_ptr<acdl_worklist_baset>(new acdl_worklist_forwardt());*/
    // [TODO]
    // worklist heuristics 
    std::unique_ptr<acdl_worklist_baset> worklist;
    if(options.get_option("acdl-propagate") == "forward")
      worklist = std::unique_ptr<acdl_worklist_baset>(new acdl_worklist_forwardt());
    /*if(options.get_option("acdl-propagate") == "backward")
      worklist = std::unique_ptr<acdl_worklist_baset>(new acdl_worklist_backward());*/
    else if(options.get_option("acdl-propagate") == "chaotic")
      worklist = std::unique_ptr<acdl_worklist_baset>(new acdl_worklist_orderedt());
    
    // conflict analysis heuristics
    std::unique_ptr<acdl_analyze_conflict_baset> conflict_analysis;
    if(options.get_option("acdl-conflict") == "first-uip")
      conflict_analysis = std::unique_ptr<acdl_analyze_conflict_baset>(new acdl_analyze_conflict_baset(domain)); //no 'new' with base class!
// SHOULD BE:
//            new acdl_conflict_analysis_firstuipt());
    //else if ...

    // decision heuristics
    std::unique_ptr<acdl_decision_heuristics_baset> decision_heuristics;
    if(options.get_option("acdl-decision") == "random")
      decision_heuristics = std::unique_ptr<acdl_decision_heuristics_baset>(new acdl_decision_heuristics_randt(domain));
    else if(options.get_option("acdl-decision") == "ordered")
      decision_heuristics = std::unique_ptr<acdl_decision_heuristics_baset>(new acdl_decision_heuristics_orderedt(domain));
    else if(options.get_option("acdl-decision") == "octagon")
      decision_heuristics = std::unique_ptr<acdl_decision_heuristics_baset>(new acdl_decision_heuristics_octagont(domain));
    else if(options.get_option("acdl-decision") == "berkmin")
      decision_heuristics = std::unique_ptr<acdl_decision_heuristics_baset>(new acdl_decision_heuristics_berkmint(domain,*conflict_analysis));
    else if(options.get_option("acdl-decision") == "range")
      decision_heuristics = std::unique_ptr<acdl_decision_heuristics_baset>(new acdl_decision_heuristics_ranget(domain));
    // ....


    // now instantiate solver
    acdl_solvert acdl_solver(options, domain, 
			     *decision_heuristics,
			     *worklist, 
			     *conflict_analysis);
    acdl_solver.set_message_handler(get_message_handler());
    property_map[property_id].result =
      acdl_solver(ssa_db.get(goto_model.goto_functions.entry_point()),
		  conjunction(assertions), conjunction(loophead_selects));
    /*acdl_solver(ssa_db.get(goto_model.goto_functions.entry_point()),
      property, true_exprt());*/
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


