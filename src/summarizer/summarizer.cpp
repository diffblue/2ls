/*******************************************************************\

Module: Summarizer

Author: Peter Schrammel

\*******************************************************************/

#include <iostream>

#include <util/simplify_expr.h>
#include <solvers/sat/satcheck.h>
#include <solvers/flattening/bv_pointers.h>
#include <util/find_symbols.h>

#include "summarizer.h"
#include "summary_db.h"

#include "../domains/ssa_analyzer.h"
#include "../domains/template_generator_summary.h"
#include "../domains/template_generator_callingcontext.h"

#include "../ssa/local_ssa.h"
#include "../ssa/simplify_ssa.h"

//#define REUSE_INVARIANTS
//#define SHOW_WHOLE_RESULT

/*******************************************************************\

Function: summarizert::initialize_preconditions()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarizert::initialize_preconditions(functionst &_functions, 
					   bool forward, 
					   bool sufficient)
{
  preconditions.clear();
  for(functionst::const_iterator it = _functions.begin(); 
      it!=_functions.end(); it++)
  {
    if(forward) preconditions[it->first] = true_exprt();
    else
    {
      local_SSAt &SSA = *it->second; 
      exprt::operandst c;
      for(local_SSAt::nodest::iterator n_it = SSA.nodes.begin();
	  n_it != SSA.nodes.end(); n_it++)
	{
	  if(n_it->assertions.empty()) continue;

	  for(local_SSAt::nodet::assertionst::iterator 
		a_it = n_it->assertions.begin();
	      a_it != n_it->assertions.end(); a_it++)
	    {
	      if(sufficient) c.push_back(not_exprt(*a_it));
              else c.push_back(*a_it);
	    }
	}
      preconditions[it->first] = conjunction(c);
    }
  }
}

/*******************************************************************\

Function: summarizert::summarize()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarizert::summarize(bool forward, bool sufficient)
{
  initialize_preconditions(ssa_db.functions(),forward,sufficient);
  for(functionst::const_iterator it = ssa_db.functions().begin(); 
      it!=ssa_db.functions().end(); it++)
  {
    status() << "\nSummarizing function " << it->first << eom;
    if(!summary_db.exists(it->first) || 
     summary_db.get(it->first).mark_recompute) 
      compute_summary_rec(it->first,false,forward,sufficient);
    else status() << "Summary for function " << it->first << 
           " exists already" << eom;
  }
}

/*******************************************************************\

Function: summarizert::summarize()

  Inputs:

 Outputs:

 Purpose: summarize from given entry point

\*******************************************************************/

void summarizert::summarize(const function_namet &function_name,
                            bool forward, bool sufficient)
{
  initialize_preconditions(ssa_db.functions(),forward,sufficient);

  status() << "\nSummarizing function " << function_name << eom;
  if(!summary_db.exists(function_name) || 
     summary_db.get(function_name).mark_recompute) 
  {
    compute_summary_rec(function_name,true,forward,sufficient);
  }
  else status() << "Summary for function " << function_name << 
	 " exists already" << eom;

  //adding preconditions to SSA for assertion check
  for(functionst::const_iterator it = ssa_db.functions().begin(); 
      it!=ssa_db.functions().end(); it++)
  {
    if(it->second->nodes.empty()) continue;
    it->second->nodes.front().constraints.push_back(preconditions[it->first]);
  }
}

/*******************************************************************\

Function: summarizert::compute_summary_rec()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarizert::compute_summary_rec(const function_namet &function_name,
				      bool context_sensitive,
				      bool forward,
				      bool sufficient)
{
  local_SSAt &SSA = ssa_db.get(function_name); 

  // recursively compute summaries for function calls
  inline_summaries(function_name,SSA,context_sensitive,forward,sufficient); 

  status() << "Analyzing function "  << function_name << eom;

  // solver
  incremental_solvert &solver = ssa_db.get_solver(function_name);
  solver.set_message_handler(get_message_handler());

  //analyze
  ssa_analyzert analyzer;
  analyzer.set_message_handler(get_message_handler());

  template_generator_summaryt template_generator(options,ssa_unwinder.get(function_name));
  template_generator.set_message_handler(get_message_handler());
  template_generator(solver.next_domain_number(),SSA,forward);

  exprt cond = preconditions[function_name];
#ifdef REUSE_INVARIANTS
  if(summary_db.exists(function_name)) //reuse existing invariants
  {
    std::ostringstream out;
    const exprt &old_inv = summary_db.get(function_name).invariant;
    out << "(original inv)" << from_expr(SSA.ns,"",old_inv) << "\n";
    debug() << out.str() << eom;
    exprt inv = ssa_unwinder.get(function_name).rename_invariant(old_inv);
    out << "(renamed inv)" << from_expr(SSA.ns,"",inv)<<"\n";
    debug() << out.str() << eom;
    cond = and_exprt(cond,inv);
  }
#endif
  analyzer(solver,SSA,cond,template_generator);

  // create summary
  summaryt summary;
  summary.params = SSA.params;
  summary.globals_in = SSA.globals_in;
  summary.globals_out = SSA.globals_out;
  if(forward) summary.precondition = preconditions.at(function_name);
  else analyzer.get_result(summary.precondition,template_generator.out_vars());
  analyzer.get_result(summary.transformer,template_generator.inout_vars());
  analyzer.get_result(summary.invariant,template_generator.loop_vars());

#ifdef SHOW_WHOLE_RESULT
  // to see all the custom template values
  exprt whole_result;
  analyzer.get_result(whole_result,template_generator.all_vars());
  debug() << "whole result: " << from_expr(SSA.ns,"",whole_result) << eom;
#endif

  if(context_sensitive && !summary.precondition.is_true())
  {
    summary.transformer = 
      implies_exprt(summary.precondition,summary.transformer);
    summary.invariant = 
      implies_exprt(summary.precondition,summary.invariant);
  }

  {
    std::ostringstream out;
    out << std::endl << "Summary for function " << function_name << std::endl;
    summary.output(out,SSA.ns);   
    status() << out.str() << eom;
  }
  
  // store summary in db
  summary_db.put(function_name,summary);

  //statistics
  //  solver_instances++;
  solver_calls += analyzer.get_number_of_solver_calls();

}

/*******************************************************************\

Function: summarizert::inline_summaries()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarizert::inline_summaries(const function_namet &function_name, 
				   local_SSAt &SSA, bool context_sensitive,
				   bool forward, bool sufficient)
{
  local_SSAt::nodest::iterator n_it = SSA.nodes.begin();

  while(true) //iterate until all function calls are gone
  {
    local_SSAt::nodet::function_callst::iterator f_it; 
    bool found = false;
    while(n_it!=SSA.nodes.end())
    {
      if(n_it->function_calls.empty()) { n_it++; continue; }

      for(f_it = n_it->function_calls.begin();
        f_it != n_it->function_calls.end(); f_it++)
      {
        assert(f_it->function().id()==ID_symbol); //no function pointers
        found = true;
        break;
      }
      if(found) break;
    }

    if(!found) break; //no more function calls

    if(!check_precondition(function_name,n_it,f_it,SSA))
    {
      if(context_sensitive) 
        compute_precondition(function_name,n_it,f_it,SSA,forward);

      irep_idt fname = to_symbol_expr(f_it->function()).get_identifier();
      status() << "Recursively summarizing function " << fname << eom;

      compute_summary_rec(fname,context_sensitive,forward,sufficient);
      summaryt summary = summary_db.get(fname);

      status() << "Replacing function " << fname << eom;
      //getting globals at call site
      local_SSAt::var_sett cs_globals_in, cs_globals_out; 
      goto_programt::const_targett loc = n_it->location;
      SSA.get_globals(loc,cs_globals_in);
      SSA.get_globals(loc,cs_globals_out,false);

      //replace
      ssa_inliner.replace(SSA.nodes,n_it,f_it,cs_globals_in,cs_globals_out,summary);
      summaries_used++;
      ssa_inliner.commit_node(n_it);
      assert(ssa_inliner.commit_nodes(SSA.nodes,n_it));
    }

    n_it++;
  }
}

/*******************************************************************\

Function: summarizert::check_precondition()

  Inputs:

 Outputs:

 Purpose: returns false if the summary needs to be recomputed

\******************************************************************/

bool summarizert::check_precondition(
  const function_namet &function_name,
  local_SSAt::nodest::iterator n_it, 
  local_SSAt::nodet::function_callst::iterator f_it,
  local_SSAt &SSA)
{
  assert(f_it->function().id()==ID_symbol); //no function pointers
  irep_idt fname = to_symbol_expr(f_it->function()).get_identifier();

  status() << "Checking precondition of " << fname << eom;

  bool precondition_holds = false;

  if(summary_db.exists(fname)) 
  {
    summaryt summary = summary_db.get(fname);
    if(summary.mark_recompute) return false;
    if(summary.precondition.is_true()) //precondition trivially holds
    {
      //getting globals at call site
      local_SSAt::var_sett cs_globals_in, cs_globals_out; 
      goto_programt::const_targett loc = n_it->location;
      SSA.get_globals(loc,cs_globals_in);
      SSA.get_globals(loc,cs_globals_out,false);

      status() << "Precondition trivially holds, replacing by summary." 
                   << eom;
      ssa_inliner.replace(SSA.nodes,n_it,f_it,
                          cs_globals_in,cs_globals_out,summary_db.get(fname));
      summaries_used++;
      precondition_holds = true;
    }
    else
    {
      exprt assertion = not_exprt(summary.precondition);

      //getting globals at call site
      local_SSAt::var_sett cs_globals_in; 
      SSA.get_globals(n_it->location,cs_globals_in);

      ssa_inliner.rename_to_caller(f_it,summary.params,
			       cs_globals_in,summary.globals_in,assertion);

      status() << "Precondition assertion for function " << fname << eom;
      n_it->assertions.push_back(assertion);

      precondition_holds = false;
    }
  }
  else if(!ssa_db.exists(fname))
  {
    status() << "Function " << fname << " not found" << eom;
    ssa_inliner.havoc(*n_it,f_it);
    precondition_holds = true;
  }
  else if(fname == function_name) 
  {
    status() << "Havoc recursive function call to " << fname << eom;
    ssa_inliner.havoc(*n_it,f_it);
    precondition_holds = true;
  }
  else 
  {
    status() << "Function " << fname << " not analyzed yet" << eom;
    return false; //function not seen yet
  }
  ssa_inliner.commit_node(n_it);
  assert(ssa_inliner.commit_nodes(SSA.nodes,n_it));

  if(precondition_holds) return true;

  // precondition check
  incremental_solvert &solver = ssa_db.get_solver(function_name);
  solver.set_message_handler(get_message_handler());
    
  solver << SSA;
  SSA.mark_nodes();

  solver.new_context();
  solver << SSA.get_enabling_exprs();
  solver << n_it->assertions.front();

  switch(solver())
  {
  case decision_proceduret::D_SATISFIABLE: {
    precondition_holds = false;

    n_it->assertions.clear();
    status() << "Precondition does not hold, need to recompute summary." << eom;
    break; }
  case decision_proceduret::D_UNSATISFIABLE: {
    precondition_holds = true;

    //getting globals at call site
    local_SSAt::var_sett cs_globals_in, cs_globals_out; 
    goto_programt::const_targett loc = n_it->location;
    SSA.get_globals(loc,cs_globals_in);
    SSA.get_globals(loc,cs_globals_out,false);

    status() << "Precondition holds, replacing by summary." << eom;
    ssa_inliner.replace(SSA.nodes,n_it,f_it,
		    cs_globals_in,cs_globals_out,summary_db.get(fname));
    ssa_inliner.commit_node(n_it);
    assert(ssa_inliner.commit_nodes(SSA.nodes,n_it));

    summaries_used++;
                
    break; }
  default: assert(false); break;
  }

  solver.pop_context();

  return precondition_holds;
}

/*******************************************************************\

Function: summarizert::compute_precondition ()

  Inputs:

 Outputs:

 Purpose: computes callee preconditions from the calling context
          for a single function call

\******************************************************************/

void summarizert::compute_precondition(
  const function_namet &function_name, 
  local_SSAt::nodest::iterator n_it, 
  local_SSAt::nodet::function_callst::iterator f_it,
  local_SSAt &SSA,
  bool forward)
{
  assert(f_it->function().id()==ID_symbol); //no function pointers
  irep_idt fname = to_symbol_expr(f_it->function()).get_identifier();

  status() << "Computing calling context for function " << fname << eom;

  // solver
  incremental_solvert &solver = ssa_db.get_solver(function_name);
  solver.set_message_handler(get_message_handler());

  ssa_analyzert analyzer;
  analyzer.set_message_handler(get_message_handler());

  template_generator_callingcontextt template_generator(options,ssa_unwinder.get(function_name));
  template_generator.set_message_handler(get_message_handler());
  template_generator(solver.next_domain_number(),SSA,n_it,f_it,forward);

  // collect globals at call site
  std::map<local_SSAt::nodet::function_callst::iterator, local_SSAt::var_sett>
    cs_globals_in;
  if(forward) SSA.get_globals(n_it->location,cs_globals_in[f_it]);
  else SSA.get_globals(n_it->location,cs_globals_in[f_it],false);

  // analyze
  analyzer(solver,SSA,preconditions[function_name],template_generator);

  // set preconditions
  local_SSAt &fSSA = ssa_db.get(fname); 

  preconditiont precondition;
  analyzer.get_result(precondition,template_generator.callingcontext_vars());
  ssa_inliner.rename_to_callee(f_it, fSSA.params,
			     cs_globals_in[f_it],fSSA.globals_in,
			     precondition);

  debug() << "Calling context for " << 
    from_expr(SSA.ns, "", *f_it) << ": " 
	  << from_expr(SSA.ns, "", precondition) << eom;

  if(preconditions[fname].is_true())
    preconditions[fname] = precondition;
  else
    preconditions[fname] = or_exprt(preconditions[fname],precondition);

  //statistics
  //  solver_instances++;
  solver_calls += analyzer.get_number_of_solver_calls();
}

