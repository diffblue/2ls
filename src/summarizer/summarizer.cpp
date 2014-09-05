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

#include "../ssa/local_ssa.h"
#include "../ssa/simplify_ssa.h"

#define PRECISE_JOIN

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

void summarizert::summarize(functionst &_functions, bool forward, 
			    bool sufficient)
{
  initialize_preconditions(_functions,forward,sufficient);
  functions = _functions;
  for(functionst::const_iterator it = functions.begin(); 
      it!=functions.end(); it++)
  {
    status() << "\nSummarizing function " << it->first << eom;
    if(!summary_db.exists(it->first)) 
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

void summarizert::summarize(functionst &_functions, 
			    const function_namet &function_name,
                            bool forward, bool sufficient)
{
  initialize_preconditions(_functions,forward,sufficient);
  functions = _functions;

  status() << "\nSummarizing function " << function_name << eom;
  if(!summary_db.exists(function_name)) 
  {
    compute_summary_rec(function_name,true,forward,sufficient);
  }
  else status() << "Summary for function " << function_name << 
	 " exists already" << eom;

  //adding preconditions to SSA for assertion check
  for(functionst::const_iterator it = _functions.begin(); 
      it!=_functions.end(); it++)
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
  local_SSAt &SSA = *functions[function_name]; 

  // recursively compute summaries for function calls
  inline_summaries(function_name,SSA,context_sensitive,forward,sufficient); 

  status() << "Analyzing function "  << function_name << eom;

  {
    std::ostringstream out;
    out << "Function body for " << function_name << 
      " to be analyzed: " << std::endl;
    for(local_SSAt::nodest::iterator n = SSA.nodes.begin(); 
        n!=SSA.nodes.end(); n++)
    {
      if(!n->empty()) n->output(out,SSA.ns);
    }
    debug() << out.str() << eom;
  }

  //check termination of function calls
  bool has_loops = false;
  bool calls_terminate = true;
  for(local_SSAt::nodest::iterator n_it = SSA.nodes.begin(); 
        n_it!=SSA.nodes.end(); n_it++)
  {
    for(local_SSAt::nodet::function_callst::iterator f_it = n_it->function_calls.begin();
        f_it != n_it->function_calls.end(); f_it++)
    {
      bool call_terminates = summary_db.get(function_name).terminates;
      if(!call_terminates) 
      {
	calls_terminate = false;
	break;
      }
    }
    if(!calls_terminate) break; //nothing to prove further
    if(n_it->loophead != SSA.nodes.end()) has_loops = true;
  }

  //analyze
  ssa_analyzert analyzer(SSA.ns, options);
  analyzer.set_message_handler(get_message_handler());

  analyzer(SSA,preconditions[function_name],forward);

  // create summary
  summaryt summary;
  summary.params = SSA.params;
  summary.globals_in = SSA.globals_in;
  summary.globals_out = SSA.globals_out;
  if(forward) summary.precondition = preconditions.at(function_name);
  else analyzer.get_postcondition(summary.precondition);
  analyzer.get_summary(summary.transformer);
#ifdef PRECISE_JOIN
  summary.transformer = implies_exprt(summary.precondition,summary.transformer);
#endif
  simplify_expr(summary.transformer, SSA.ns);

#if 0 
  simplify_expr(summary.precondition, SSA.ns); //does not help
#endif 

  //check termination
  debug() << "function calls " << 
    (calls_terminate ? "terminate" : " do not terminate") << eom;
  debug() << "function " << 
    (has_loops ? "has loops" : " does not have loops") << eom;
  if(calls_terminate && has_loops) 
  {
    //TODO: compute ranking functions
  }
  else if(!calls_terminate) summary.terminates = false;
  else if(!has_loops) summary.terminates = true;

  {
    std::ostringstream out;
    out << std::endl << "Summary for function " << function_name << std::endl;
    summary.output(out,SSA.ns);   
    status() << out.str() << eom;
  }

  // store summary in db
  if(summary_db.exists(function_name)) 
  {
    summaryt old_summary = summary_db.get(function_name);
    join_summaries(old_summary,summary);
  }
  summary_db.put(function_name,summary);
  
  // Add loop invariants as constraints back into SSA.
  // We simply use the last CFG node. It would be prettier to put
  // these close to the loops.
  exprt inv;
  analyzer.get_loop_invariants(inv);
  assert(SSA.nodes.begin()!=SSA.nodes.end());
  SSA.nodes.back().constraints.push_back(inv);

  status() << "Adding loop invariant: " << from_expr(SSA.ns, "", inv) << eom;

  //statistics
  solver_instances++;
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
  ssa_inlinert inliner;
  inliner.set_message_handler(get_message_handler());

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

    if(!check_precondition(function_name,n_it,f_it,SSA,inliner))
    {
      if(context_sensitive) 
        compute_precondition(function_name,n_it,f_it,SSA,inliner,forward);

      irep_idt fname = to_symbol_expr(f_it->function()).get_identifier();
      status() << "Recursively summarizing function " << fname << eom;

      compute_summary_rec(fname,context_sensitive,forward,sufficient);
      summaryt summary = summary_db.get(fname);

      status() << "Replacing function " << fname << eom;
      //getting globals at call site
      local_SSAt::var_sett cs_globals_in, cs_globals_out; 
      goto_programt::const_targett loc = n_it->location;
      SSA.get_globals(loc,cs_globals_in);
      assert(loc!=SSA.goto_function.body.instructions.end());
      SSA.get_globals(++loc,cs_globals_out);

      //replace
      inliner.replace(SSA.nodes,n_it,f_it,cs_globals_in,cs_globals_out,summary);
      summaries_used++;
      inliner.commit_node(n_it);
      assert(inliner.commit_nodes(SSA.nodes,n_it));
    }

    n_it++;
  }
}


  //obsolete
/*******************************************************************\

Function: summarizert::inline_summaries()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
/*
void summarizert::inline_summaries(const function_namet &function_name, 
				   local_SSAt &SSA, bool recursive, 
				   bool always_recompute)
{
  ssa_inlinert inliner;
  inliner.set_message_handler(get_message_handler());

  // replace calls with summaries
  // TODO: functions with pointers passed as parameters
  for(local_SSAt::nodest::iterator n_it = SSA.nodes.begin();
      n_it != SSA.nodes.end(); n_it++)
  {
    if(n_it->function_calls.empty()) continue;


    for(local_SSAt::nodet::function_callst::iterator 
        f_it = n_it->function_calls.begin();
        f_it != n_it->function_calls.end(); f_it++)
    {
      assert(f_it->function().id()==ID_symbol); //no function pointers
      irep_idt fname = to_symbol_expr(f_it->function()).get_identifier();

      summaryt summary; 
      bool recompute = false || always_recompute;
      if(!always_recompute) 
      {
        // replace call with summary if it exists 
        if(summary_db.exists(fname)) 
        {
          status() << "Using existing summary for function " << fname << eom;
  	  summary = summary_db.get(fname);
        }
        // compute summary if function_name in functions
        else if(functions.find(fname)!=functions.end() && recursive &&
                fname!=function_name) // havoc recursive calls
	{
          recompute = true;
	}
        else // havoc function call by default
        {
          status() << "Function " << fname << " not found" << eom;
          inliner.havoc(*n_it,f_it);
          continue;
        }
      }
      if(recompute) 
      {
        status() << "Recursively summarizing function " << fname << eom;
        compute_summary_rec(fname);
        summary = summary_db.get(fname);
      }

      status() << "Replacing function " << fname << eom;
      //getting globals at call site
      local_SSAt::var_sett cs_globals_in, cs_globals_out; 
      goto_programt::const_targett loc = n_it->location;
      SSA.get_globals(loc,cs_globals_in);
      assert(loc!=SSA.goto_function.body.instructions.end());
      SSA.get_globals(++loc,cs_globals_out);

#if 0
      std::cout << "globals at call site: ";
      for(summaryt::var_sett::const_iterator it = cs_globals_out.begin();
          it != cs_globals_out.end(); it++)
         std::cout << from_expr(functions[function_name]->ns,"",*it) << " ";
      std::cout << std::endl;
#endif

      //replace
      inliner.replace(SSA.nodes,n_it,f_it,cs_globals_in,cs_globals_out,summary);
      summaries_used++;
    }
    inliner.commit_node(n_it);
  }
  assert(inliner.commit_nodes(SSA.nodes,SSA.nodes.end()));
}
*/

/*******************************************************************\

Function: summarizert::join_summaries()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarizert::join_summaries(const summaryt &existing_summary, 
				 summaryt &new_summary)
{
  assert(existing_summary.params == new_summary.params);
  assert(existing_summary.globals_in == new_summary.globals_in);
  assert(existing_summary.globals_out == new_summary.globals_out);
  new_summary.precondition = or_exprt(existing_summary.precondition,
					   new_summary.precondition);
#ifdef PRECISE_JOIN
  new_summary.transformer = and_exprt(existing_summary.transformer,
    implies_exprt(new_summary.precondition,new_summary.transformer));
#else
  new_summary.transformer = or_exprt(existing_summary.transformer,
    new_summary.transformer);
#endif
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
  local_SSAt &SSA,
  ssa_inlinert &inliner)
{
  assert(f_it->function().id()==ID_symbol); //no function pointers
  irep_idt fname = to_symbol_expr(f_it->function()).get_identifier();

  status() << "Checking precondition of " << fname << eom;

  bool precondition_holds = false;

  if(summary_db.exists(fname)) 
  {
    summaryt summary = summary_db.get(fname);
    if(summary.precondition.is_true()) //precondition trivially holds
    {
      //getting globals at call site
      local_SSAt::var_sett cs_globals_in, cs_globals_out; 
      goto_programt::const_targett loc = n_it->location;
      SSA.get_globals(loc,cs_globals_in);
      assert(loc!=SSA.goto_function.body.instructions.end());
      SSA.get_globals(++loc,cs_globals_out);

      status() << "Precondition trivially holds, replacing by summary." 
                   << eom;
      inliner.replace(SSA.nodes,n_it,f_it,
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

      inliner.rename_to_caller(f_it,summary.params,
			       cs_globals_in,summary.globals_in,assertion);

      status() << "Precondition assertion for function " << fname << eom;
      n_it->assertions.push_back(assertion);

      precondition_holds = false;
    }
  }
  else if(functions.find(fname)==functions.end())
  {
    status() << "Function " << fname << " not found" << eom;
    inliner.havoc(*n_it,f_it);
    precondition_holds = true;
  }
  else if(fname == function_name) 
  {
    status() << "Havoc recursive function call to " << fname << eom;
    inliner.havoc(*n_it,f_it);
    precondition_holds = true;
  }
  else 
  {
    status() << "Function " << fname << " not analyzed yet" << eom;
    return false; //function not seen yet
  }
  inliner.commit_node(n_it);
  assert(inliner.commit_nodes(SSA.nodes,n_it));

  if(precondition_holds) return true;

  // precondition check
  satcheckt satcheck;
  bv_pointerst solver(SSA.ns, satcheck);
  
  satcheck.set_message_handler(get_message_handler());
  solver.set_message_handler(get_message_handler());
    
  solver << SSA;
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
    assert(loc!=SSA.goto_function.body.instructions.end());
    SSA.get_globals(++loc,cs_globals_out);

    status() << "Precondition holds, replacing by summary." << eom;
    inliner.replace(SSA.nodes,n_it,f_it,
		    cs_globals_in,cs_globals_out,summary_db.get(fname));
    inliner.commit_node(n_it);
    assert(inliner.commit_nodes(SSA.nodes,n_it));

    summaries_used++;
                
    break; }
  default: assert(false); break;
  }

  //statistics
  solver_instances++;
  solver_calls++;

  return precondition_holds;
}

/*******************************************************************\

Function: summarizert::check_preconditions()

  Inputs:

 Outputs:

 Purpose:

\******************************************************************/
/*
void summarizert::check_preconditions(
  const function_namet &function_name, 
  local_SSAt &SSA,
  ssa_inlinert &inliner)
{
  status() << "Checking preconditions" << eom;

  // add precondition assertion for each call
  for(local_SSAt::nodest::iterator n_it = SSA.nodes.begin(); 
      n_it!=SSA.nodes.end(); n_it++)
  {
    for(local_SSAt::nodet::function_callst::iterator 
        f_it = n_it->function_calls.begin();
        f_it != n_it->function_calls.end(); f_it++)
    {
      assert(f_it->function().id()==ID_symbol); //no function pointers
      irep_idt fname = to_symbol_expr(f_it->function()).get_identifier();

      if(summary_db.exists(fname)) 
      {
	summaryt summary = summary_db.get(fname);
        if(summary.precondition.is_true()) //precondition trivially holds
	{
	  //getting globals at call site
	  local_SSAt::var_sett cs_globals_in, cs_globals_out; 
	  goto_programt::const_targett loc = n_it->location;
	  SSA.get_globals(loc,cs_globals_in);
	  assert(loc!=SSA.goto_function.body.instructions.end());
	  SSA.get_globals(++loc,cs_globals_out);

          status() << "Precondition trivially holds, replacing by summary." 
                   << eom;
          inliner.replace(SSA.nodes,n_it,f_it,
                          cs_globals_in,cs_globals_out,summary_db.get(fname));
          summaries_used++;
	  continue;
	}

	exprt assertion = not_exprt(summary.precondition);

	//getting globals at call site
	local_SSAt::var_sett cs_globals_in; 
	SSA.get_globals(n_it->location,cs_globals_in);

	inliner.rename_to_caller(f_it,summary.params,
				 cs_globals_in,summary.globals_in,assertion);

        n_it->assertions.push_back(assertion);
        status() << "Precondition assertion for function " << fname << eom;
      }
      else if(functions.find(fname)==functions.end())
      {
        status() << "Function " << fname << " not found" << eom;
        inliner.havoc(*n_it,f_it);
        continue;
      }
    }
    inliner.commit_node(n_it);
  }
  assert(inliner.commit_nodes(SSA.nodes,SSA.nodes.end()));

  // non-incremental precondition check, TODO: make incremental
  for(local_SSAt::nodest::iterator n_it = SSA.nodes.begin(); 
      n_it!=SSA.nodes.end(); n_it++)
  {
    if(!n_it->function_calls.empty() &&
       !n_it->assertions.empty())
    {
      assert(n_it->assertions.size()==1);

      local_SSAt::nodet::function_callst::iterator 
        f_it = n_it->function_calls.begin();      
      assert(f_it->function().id()==ID_symbol); //no function pointers
      irep_idt fname = to_symbol_expr(f_it->function()).get_identifier();

      status() << "Checking precondition for function " << fname << eom;
      
      satcheckt satcheck;
      bv_pointerst solver(SSA.ns, satcheck);
  
      satcheck.set_message_handler(get_message_handler());
      solver.set_message_handler(get_message_handler());
    
      solver << SSA;
      solver << n_it->assertions.front();

      switch(solver())
      {
	case decision_proceduret::D_SATISFIABLE:
          n_it->assertions.clear();
          status() << "Precondition does not hold, need to recompute summary." << eom;
          break;
	case decision_proceduret::D_UNSATISFIABLE:
	{
          //TODO: assume precondition for next check

          n_it->assertions.clear();

	  //getting globals at call site
	  local_SSAt::var_sett cs_globals_in, cs_globals_out; 
	  goto_programt::const_targett loc = n_it->location;
	  SSA.get_globals(loc,cs_globals_in);
	  assert(loc!=SSA.goto_function.body.instructions.end());
	  SSA.get_globals(++loc,cs_globals_out);

          status() << "Precondition holds, replacing by summary." << eom;
          inliner.replace(SSA.nodes,n_it,f_it,
                          cs_globals_in,cs_globals_out,summary_db.get(fname));
          summaries_used++;
                
          break;
	}
        default: assert(false); break;
      }

      //statistics
      solver_instances++;
      solver_calls++;
    }
    inliner.commit_node(n_it);
  }
  assert(inliner.commit_nodes(SSA.nodes,SSA.nodes.end()));

  //now, only function calls which need recomputing of their summaries are left
}
*/
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
  ssa_inlinert &inliner,
  bool forward)
{
  assert(f_it->function().id()==ID_symbol); //no function pointers
  irep_idt fname = to_symbol_expr(f_it->function()).get_identifier();

  status() << "Computing calling context for function " << fname << eom;

  ssa_analyzert analyzer(SSA.ns, options);
  analyzer.set_message_handler(get_message_handler());
  analyzer.compute_calling_contexts = true;

  // collect globals at call site
  std::map<local_SSAt::nodet::function_callst::iterator, local_SSAt::var_sett>
    cs_globals_in;
 
  SSA.get_globals(n_it->location,cs_globals_in[f_it]);
  analyzer.calling_context_vars[f_it].insert(
  SSA.globals_in.begin(),SSA.globals_in.end());

  if(cs_globals_in.empty()) return; //nothing to do

  // analyze
  analyzer(SSA,preconditions[function_name],forward);

  ssa_analyzert::calling_contextst calling_contexts;
  analyzer.get_calling_contexts(calling_contexts);

  // set preconditions
  local_SSAt &fSSA = *functions[fname]; 

  preconditiont precondition = calling_contexts[f_it];
  inliner.rename_to_callee(f_it, fSSA.params,
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
  solver_instances++;
  solver_calls += analyzer.get_number_of_solver_calls();
}


/*******************************************************************\

Function: summarizert::compute_preconditions()

  Inputs:

 Outputs:

 Purpose: computes callee preconditions from the calling context
          for all function calls

\******************************************************************/
/*
void summarizert::compute_preconditions(
  const function_namet &function_name, 
  local_SSAt &SSA,
  ssa_inlinert &inliner)
{
  status() << "Computing preconditions from calling context" << eom;

  ssa_analyzert analyzer(SSA.ns, options);
  analyzer.set_message_handler(get_message_handler());
  analyzer.compute_calling_contexts = true;

  // collect globals at call site
  std::map<local_SSAt::nodet::function_callst::iterator, local_SSAt::var_sett>
    cs_globals_in;
 
  for(local_SSAt::nodest::iterator n_it = SSA.nodes.begin(); 
      n_it!=SSA.nodes.end(); n_it++)
  {
    for(local_SSAt::nodet::function_callst::iterator 
        f_it = n_it->function_calls.begin();
        f_it != n_it->function_calls.end(); f_it++)
    {
      assert(f_it->function().id()==ID_symbol); //no function pointers

      SSA.get_globals(n_it->location,cs_globals_in[f_it]);
      analyzer.calling_context_vars[f_it].insert(
        SSA.globals_in.begin(),SSA.globals_in.end());
    }
  }

  if(cs_globals_in.empty()) return; //nothing to do

  // analyze
  analyzer(SSA,preconditions[function_name]);

  ssa_analyzert::calling_contextst calling_contexts;
  analyzer.get_calling_contexts(calling_contexts);

  // set preconditions
  for(ssa_analyzert::calling_contextst::iterator it = calling_contexts.begin();
      it != calling_contexts.end(); it++)
  {
    const irep_idt &fname = 
      to_symbol_expr(it->first->function()).get_identifier();
    local_SSAt &fSSA = *functions[fname]; 

    preconditiont precondition = it->second;
    inliner.rename_to_callee(it->first, fSSA.params,
			     cs_globals_in[it->first],fSSA.globals_in,
			     precondition);

    debug() << "Calling context for " << 
               from_expr(SSA.ns, "", *it->first) << ": " 
	    << from_expr(SSA.ns, "", precondition) << eom;

    if(preconditions[fname].is_true())
      preconditions[fname] = precondition;
    else
      preconditions[fname] = or_exprt(preconditions[fname],precondition);
  }

  //statistics
  solver_instances++;
  solver_calls += analyzer.get_number_of_solver_calls();
}
*/
