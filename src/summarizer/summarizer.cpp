/*******************************************************************\

Module: Summarizer

Author: Peter Schrammel

\*******************************************************************/

#include <iostream>

#include <util/simplify_expr.h>
#include <solvers/sat/satcheck.h>
#include <solvers/flattening/bv_pointers.h>
#include <solvers/smt2/smt2_dec.h>
#include <util/find_symbols.h>

#include "summarizer.h"
#include "summary_db.h"

#include "../domains/ssa_analyzer.h"
#include "../domains/template_generator_summary.h"
#include "../domains/template_generator_callingcontext.h"
#include "../domains/template_generator_ranking.h"

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

void summarizert::summarize(bool forward, bool sufficient)
{
  initialize_preconditions(ssa_db.functions(),forward,sufficient);
  for(functionst::const_iterator it = ssa_db.functions().begin(); 
      it!=ssa_db.functions().end(); it++)
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

void summarizert::summarize(const function_namet &function_name,
                            bool forward, bool sufficient)
{
  initialize_preconditions(ssa_db.functions(),forward,sufficient);

  status() << "\nSummarizing function " << function_name << eom;
  if(!summary_db.exists(function_name)) 
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
  
  bool calls_terminate = true;
  // recursively compute summaries for function calls
  inline_summaries(function_name,SSA,context_sensitive,forward,sufficient,
    calls_terminate); 

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
    out << "(enable) " << from_expr(SSA.ns, "", SSA.get_enabling_exprs()) << "\n";
    debug() << out.str() << eom;
  }

  bool has_loops = false;  
  if(options.get_bool_option("termination"))
  {
    for(local_SSAt::nodest::iterator n_it = SSA.nodes.begin(); 
        n_it!=SSA.nodes.end(); n_it++)
    {
      if(n_it->loophead != SSA.nodes.end()) has_loops = true;
    }
  }

  //analyze
  ssa_analyzert analyzer(SSA.ns, options);
  analyzer.set_message_handler(get_message_handler());

  template_generator_summaryt template_generator(options,ssa_unwinder.get(function_name));
  template_generator(SSA,forward);

  analyzer(SSA,preconditions[function_name],template_generator);

  // create summary
  summaryt summary;
  summary.params = SSA.params;
  summary.globals_in = SSA.globals_in;
  summary.globals_out = SSA.globals_out;
  if(forward) summary.precondition = preconditions.at(function_name);
  else analyzer.get_result(summary.precondition,template_generator.out_vars());
  analyzer.get_result(summary.transformer,template_generator.inout_vars());
#ifdef PRECISE_JOIN
  summary.transformer = implies_exprt(summary.precondition,summary.transformer);
#endif
  simplify_expr(summary.transformer, SSA.ns);

#if 0 
  simplify_expr(summary.precondition, SSA.ns); //does not help
#endif 

  // Add loop invariants as constraints back into SSA.
  // We simply use the last CFG node. It would be prettier to put
  // these close to the loops.
  exprt inv;
  analyzer.get_result(inv,template_generator.loop_vars());
  status() << "Adding loop invariant: " << from_expr(SSA.ns, "", inv) << eom;
  // always do precise join here (otherwise we have to store the loop invariant
  // in the summary and handle its updates like the transformer's
  inv = implies_exprt(summary.precondition,inv);
  assert(SSA.nodes.begin()!=SSA.nodes.end());
  SSA.nodes.back().constraints.push_back(inv);

  //check termination
  if(options.get_bool_option("termination"))
  {
    debug() << "function calls " << 
      (calls_terminate ? "terminate" : " do not terminate") << eom;
    debug() << "function " << 
      (has_loops ? "has loops" : " does not have loops") << eom;
    if(calls_terminate && has_loops) 
    {
      template_generator_rankingt template_generator(options,ssa_unwinder.get(function_name));
      template_generator(SSA,forward);

      ssa_analyzert analyzer1(SSA.ns, options);
      analyzer1.set_message_handler(get_message_handler());
      analyzer1.compute_ranking_functions = true;
      analyzer1(SSA,preconditions[function_name],template_generator);
      analyzer1.get_result(summary.termination_argument,template_generator.all_vars());

      //extract information whether there a ranking function was found for all loops
      summary.terminates = check_termination_argument(summary.termination_argument); 
     
      //statistics
      solver_instances++;
      solver_calls += analyzer1.get_number_of_solver_calls();
    }
    else if(!calls_terminate) summary.terminates = false;
    else if(!has_loops) summary.terminates = true;
  }

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
				   bool forward, bool sufficient,
                                   bool &calls_terminate)
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

      //get information about callee termination
      if(options.get_bool_option("termination"))
      {
	if(!summary_db.get(fname).terminates) 
	{
	  calls_terminate = false;
	  break;
	}
      }
      else calls_terminate = false;
    }

    n_it++;
  }
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
  else if(!ssa_db.exists(fname))
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
  smt2_dect solver(SSA.ns, "summarizer", "", "QF_BV", smt2_dect::Z3);
  //bv_pointerst solver(SSA.ns, satcheck);
  //bv_pointerst solver(SSA.ns, smt);
  
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

  template_generator_callingcontextt template_generator(options,ssa_unwinder.get(function_name));
  template_generator(SSA,n_it,f_it,forward);

  // collect globals at call site
  std::map<local_SSAt::nodet::function_callst::iterator, local_SSAt::var_sett>
    cs_globals_in;
  if(forward) SSA.get_globals(n_it->location,cs_globals_in[f_it]);
  else SSA.get_globals((++n_it)->location,cs_globals_in[f_it]);

  // analyze
  analyzer(SSA,preconditions[function_name],template_generator);

  // set preconditions
  local_SSAt &fSSA = ssa_db.get(fname); 

  preconditiont precondition;
  analyzer.get_result(precondition,template_generator.callingcontext_vars());
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

Function: summarizert::check_termination_argument()

  Inputs:

 Outputs:

 Purpose: checks whether a termination argument implies termination

\******************************************************************/

bool summarizert::check_termination_argument(exprt expr)
{
  if(expr.is_false()) return true;
  // should be of the form /\_i g_i => R_i
  if(expr.id()==ID_and)
  {
    for(exprt::operandst::iterator it = expr.operands().begin(); 
      it != expr.operands().end(); it++)
    {
      if(it->is_false()) return true;
      assert(it->id()==ID_implies);
      if(it->op1().is_true()) return false;
    }
  }
  else
  {
    if(expr.id()==ID_implies)
    {
      if(expr.op1().is_true()) return false;
    }
    else return !expr.is_true();
  }
  return true;
}
