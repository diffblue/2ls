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

Function: summarizert::summarize()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

summaryt summarizert::summarize(functiont &function, 
				const preconditiont &precondition)
{
  functions.clear();
  preconditions.clear();
  functions[function.first] = function.second;
  preconditions[function.first] = precondition; 
  run();
  return summary_db.get(function.first);
}

/*******************************************************************\

Function: summarizert::summarize()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

summaryt summarizert::summarize(functiont &function)
{ 
  return summarize(function,true_exprt()); 
} 

/*******************************************************************\

Function: summarizert::summarize()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarizert::summarize(functionst &_functions)
{
  preconditionst _preconditions;
  for(functionst::const_iterator it = _functions.begin(); 
      it!=_functions.end(); it++)
  {
    _preconditions[it->first] = true_exprt();
  }
  summarize(_functions,_preconditions);
}

/*******************************************************************\

Function: summarizert::summarize()

  Inputs:

 Outputs:

 Purpose: summarize from given entry point

\*******************************************************************/

void summarizert::summarize(functionst &_functions, 
			    const function_namet &function_name)
{
  functions = _functions;

  preconditions.clear();
  for(functionst::const_iterator it = _functions.begin(); 
      it!=_functions.end(); it++)
  {
    preconditions[it->first] = true_exprt();
  }

  status() << "\nSummarizing function " << function_name << eom;
  if(!summary_db.exists(function_name)) 
  {
    compute_summary_rec(function_name);
  }
  else status() << "Summary for function " << function_name << 
	 " exists already" << eom;
}

/*******************************************************************\

Function: summarizert::summarize()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarizert::summarize(functionst &_functions,
			    const preconditionst &_preconditions)
{
  functions = _functions;
  preconditions = _preconditions;
  run();
}

/*******************************************************************\

Function: summarizert::run()

  Inputs:

 Outputs:

 Purpose: just summarize each function in functions

\*******************************************************************/

void summarizert::run()
{
  for(functionst::const_iterator it = functions.begin(); 
      it!=functions.end(); it++)
  {
    status() << "\nSummarizing function " << it->first << eom;
    if(!summary_db.exists(it->first)) compute_summary_rec(it->first);
    else status() << "Summary for function " << it->first << 
           " exists already" << eom;
  }
}

/*******************************************************************\

Function: summarizert::compute_summary_rec()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarizert::compute_summary_rec(const function_namet &function_name)
{
  local_SSAt &SSA = *functions[function_name]; 

  // recursively compute summaries for function calls
  check_preconditions(function_name,SSA);
  compute_preconditions(function_name,SSA);
  inline_summaries(function_name,SSA,true,true); 

  status() << "Analyzing function "  << function_name << eom;

  {
    std::ostringstream out;
    out << "Function body for " << function_name << 
      " to be analyzed: " << std::endl;
    for(local_SSAt::nodest::iterator n = SSA.nodes.begin(); 
        n!=SSA.nodes.end(); n++)
    {
      if(!n->second.empty()) n->second.output(out,SSA.ns);
    }
    debug() << out.str() << eom;
  }

  //analyze
  ssa_analyzert analyzer(SSA.ns, options);
  analyzer.set_message_handler(get_message_handler());

  analyzer(SSA,preconditions[function_name]);

  // create summary
  summaryt summary;
  summary.params =SSA.params;
  summary.globals_in =SSA.globals_in;
  summary.globals_out =SSA.globals_out;
  summary.precondition = preconditions.at(function_name);
  analyzer.get_summary(summary.transformer);
#ifdef PRECISE_JOIN
  summary.transformer = implies_exprt(summary.precondition,summary.transformer);
#endif
  simplify_expr(summary.transformer, SSA.ns);

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
  goto_programt::const_targett loc=
    SSA.goto_function.body.instructions.end();
  loc--;
  local_SSAt::nodet &node=SSA.nodes[loc];
  exprt inv;
  analyzer.get_loop_invariants(inv);
  node.constraints.push_back(inv);

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
				   local_SSAt &SSA, bool recursive, 
				   bool always_recompute)
{
  ssa_inlinert inliner;
  inliner.set_message_handler(get_message_handler());

  // replace calls with summaries
  // TODO: functions with pointers passed as parameters
  forall_goto_program_instructions(i_it, SSA.goto_function.body)
  {
    if(!i_it->is_function_call()) continue;

    local_SSAt::nodest::iterator n = SSA.nodes.find(i_it);

    for(local_SSAt::nodet::function_callst::iterator 
        f_it = n->second.function_calls.begin();
        f_it != n->second.function_calls.end(); f_it++)
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
           inliner.havoc(n->second,f_it);
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
      goto_programt::const_targett loc = n->first;
      SSA.get_globals(loc,cs_globals_in);
      assert(loc!=SSA.goto_function.body.instructions.end());
      SSA.get_globals(++loc,cs_globals_out);

      /*      for(summaryt::var_sett::const_iterator it = summary.globals_in.begin();
          it != summary.globals_in.end(); it++)
	  std::cout << "global " << SSA.read_rhs(*it,loc) << std::endl; */
    
#if 0
      std::cout << "globals at call site: ";
      for(summaryt::var_sett::const_iterator it = cs_globals_out.begin();
          it != cs_globals_out.end(); it++)
         std::cout << from_expr(functions[function_name]->ns,"",*it) << " ";
      std::cout << std::endl;
#endif

      //replace
      inliner.replace(SSA.nodes,n,f_it,cs_globals_in,cs_globals_out,summary);
    }
    inliner.commit_node(n);
  }
  inliner.commit_nodes(SSA.nodes);
}

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

Function: summarizert::check_preconditions()

  Inputs:

 Outputs:

 Purpose:

\******************************************************************/

void summarizert::check_preconditions(
  const function_namet &function_name, 
  local_SSAt &SSA)
{
  status() << "Checking preconditions" << eom;

  ssa_inlinert inliner;
  inliner.set_message_handler(get_message_handler());

  // add precondition assertion for each call
  for(local_SSAt::nodest::iterator n = SSA.nodes.begin(); 
      n!=SSA.nodes.end(); n++)
  {
    for(local_SSAt::nodet::function_callst::iterator 
        f_it = n->second.function_calls.begin();
        f_it != n->second.function_calls.end(); f_it++)
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
	  goto_programt::const_targett loc = n->first;
	  SSA.get_globals(loc,cs_globals_in);
	  assert(loc!=SSA.goto_function.body.instructions.end());
	  SSA.get_globals(++loc,cs_globals_out);

          status() << "Precondition trivially holds, replacing by summary." 
                   << eom;
          inliner.replace(SSA.nodes,n,f_it,
                          cs_globals_in,cs_globals_out,summary_db.get(fname));
	  continue;
	}

	exprt assertion = not_exprt(summary.precondition);

	//getting globals at call site
	local_SSAt::var_sett cs_globals_in; 
	SSA.get_globals(n->first,cs_globals_in);

	inliner.rename_to_caller(f_it,summary.params,
				 cs_globals_in,summary.globals_in,assertion);

        n->second.assertions.push_back(assertion);
        status() << "Precondition assertion for function " << fname << eom;
      }
      else if(functions.find(fname)==functions.end())
      {
        status() << "Function " << fname << " not found" << eom;
        inliner.havoc(n->second,f_it);
        continue;
      }
    }
    inliner.commit_node(n);
  }
  inliner.commit_nodes(SSA.nodes);

  // non-incremental precondition check, TODO: make incremental
  for(local_SSAt::nodest::iterator n = SSA.nodes.begin(); 
      n!=SSA.nodes.end(); n++)
  {
    if(!n->second.function_calls.empty() &&
       !n->second.assertions.empty())
    {
      assert(n->second.assertions.size()==1);

      local_SSAt::nodet::function_callst::iterator 
        f_it = n->second.function_calls.begin();      
      assert(f_it->function().id()==ID_symbol); //no function pointers
      irep_idt fname = to_symbol_expr(f_it->function()).get_identifier();

      status() << "Checking precondition for function " << fname << eom;
      
      satcheckt satcheck;
      bv_pointerst solver(SSA.ns, satcheck);
  
      satcheck.set_message_handler(get_message_handler());
      solver.set_message_handler(get_message_handler());
    
      solver << SSA;
      solver << n->second.assertions.front();

      switch(solver())
      {
	case decision_proceduret::D_SATISFIABLE:
          n->second.assertions.clear();
          status() << "Precondition does not hold, need to recompute summary." << eom;
          break;
	case decision_proceduret::D_UNSATISFIABLE:
	{
          //TODO: assume precondition for next check

          n->second.assertions.clear();

	  //getting globals at call site
	  local_SSAt::var_sett cs_globals_in, cs_globals_out; 
	  goto_programt::const_targett loc = n->first;
	  SSA.get_globals(loc,cs_globals_in);
	  assert(loc!=SSA.goto_function.body.instructions.end());
	  SSA.get_globals(++loc,cs_globals_out);

          status() << "Precondition holds, replacing by summary." << eom;
          inliner.replace(SSA.nodes,n,f_it,
                          cs_globals_in,cs_globals_out,summary_db.get(fname));
                
          break;
	}
        default: assert(false); break;
      }

      //statistics
      solver_instances++;
      solver_calls++;
    }
    inliner.commit_node(n);
  }
  inliner.commit_nodes(SSA.nodes);

  //now, only function calls which need recomputing of their summaries are left
}

/*******************************************************************\

Function: summarizert::compute_preconditions()

  Inputs:

 Outputs:

 Purpose: computes callee preconditions from the calling context

\******************************************************************/

void summarizert::compute_preconditions(
  const function_namet &function_name, 
  local_SSAt &SSA)
{
  status() << "Computing preconditions from calling context" << eom;

  ssa_inlinert inliner;
  inliner.set_message_handler(get_message_handler());

  ssa_analyzert analyzer(SSA.ns, options);
  analyzer.set_message_handler(get_message_handler());
  analyzer.compute_calling_contexts = true;

  // collect globals at call site
  std::map<local_SSAt::nodet::function_callst::iterator, local_SSAt::var_sett>
    cs_globals_in;
 
  for(local_SSAt::nodest::iterator n = SSA.nodes.begin(); 
      n!=SSA.nodes.end(); n++)
  {
    for(local_SSAt::nodet::function_callst::iterator 
        f_it = n->second.function_calls.begin();
        f_it != n->second.function_calls.end(); f_it++)
    {
      assert(f_it->function().id()==ID_symbol); //no function pointers

      SSA.get_globals(n->first,cs_globals_in[f_it]);
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
