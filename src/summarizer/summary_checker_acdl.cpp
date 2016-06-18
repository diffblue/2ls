/*******************************************************************\

Module: Summary Checker using ACDL

Author: Peter Schrammel

\*******************************************************************/

#include <util/simplify_expr.h>

#include "summary_checker_acdl.h"

#include "../acdl/acdl_solver.h"
#include "../acdl/acdl_domain.h"
//#include "../acdl/acdl_decision_heuristics_cond.h"
#include "../acdl/acdl_decision_heuristics.h"
#include "../acdl/acdl_worklist_ordered.h"
#include "../acdl/acdl_conflict_analysis_base.h"

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
        exprt property=*a_it;
        
        if(simplify) property=simplify_expr(property, SSA.ns);
        property_map[property_id].location = i_it;

	//TODO: make this incremental
	acdl_domaint acdl_domain(options,SSA,ssa_db,ssa_local_unwinder);
	acdl_decision_heuristicst acdl_decision_heuristics(acdl_domain);
	// acdl_decision_heuristics_condt acdl_decision_heuristics(acdl_domain);
	acdl_worklist_orderedt acdl_worklist;
	acdl_conflict_analysis_baset acdl_conflict_analysist;
	acdl_solvert acdl_solver(options, acdl_domain, acdl_decision_heuristics,
				 acdl_worklist, acdl_conflict_analysist);
	acdl_solver.set_message_handler(get_message_handler());
	property_map[property_id].result =
	  acdl_solver(ssa_db.get(goto_model.goto_functions.entry_point()),
		      property, conjunction(loophead_selects));

//	exprt property_value = simplify_expr(acdl_solver.get(property), SSA.ns);
      }
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


