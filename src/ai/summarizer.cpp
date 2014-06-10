/*******************************************************************\

Module: Summarizer

Author: Peter Schrammel

\*******************************************************************/

#include <iostream>

#include "summarizer.h"
#include "summary_store.h"

#include "concrete_transformers.h"
#include "interval_map_domain.h"




/*******************************************************************\

Function: summarizert::summarize()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

summaryt summarizert::summarize(const functiont &function, const preconditiont &precondition)
{
  functions.clear();
  preconditions.clear();
  functions[function.first] = function.second;
  preconditions[function.first] = precondition; 
  run();
  return summary_store.get(function.first);
}

/*******************************************************************\

Function: summarizert::summarize()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

summaryt summarizert::summarize(const functiont &function)
{ 
  return summarize(function,true_exprt()); 
} 

/*******************************************************************\

Function: summarizert::summarize()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarizert::summarize(const functionst &_functions)
{
  preconditionst _preconditions;
  for(functionst::const_iterator it = _functions.begin(); it!=_functions.end(); it++)
  {
    _preconditions[it->first] = true_exprt();
  }
  summarize(_functions,_preconditions);
}

/*******************************************************************\

Function: summarizert::summarize()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarizert::summarize(const functionst &_functions,const preconditionst &_preconditions)
{
  functions = _functions;
  preconditions = _preconditions;
  run();
}

/*******************************************************************\

Function: summarizert::run()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarizert::run()
{

  //TODO: compute fixed point (if any descendents in the call graph are updated)
  //TODO: make context sensitive (currently, only globally given preconditions are used)
  //TODO: replace simple iterator by something following the call graph
  for(functionst::const_iterator it = functions.begin(); it!=functions.end(); it++)
  {
    status() << "Summarizing function " << it->first << eom;
    if(!summary_store.exists(it->first)) compute_summary_rec(it->first);
    else status() << "Summary for function " << it->first << " exists already" << eom;
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
  local_SSAt::nodest nodes = functions[function_name]->nodes; //copy
  inline_summaries(function_name,nodes,true); 
  // functions[function_name]->get_entry_exit_vars();

  std::ostringstream out;
  out << "Function body for " << function_name << " to be analyzed: " << std::endl;
  for(local_SSAt::nodest::iterator n = nodes.begin(); n!=nodes.end(); n++)
    if(!n->second.empty()) n->second.output(out,functions[function_name]->ns);
  debug() << out.str() << eom;

  /*
  // collect the transformer  
  concrete_transformerst transformers(functions[function_name]->ns, nodes);  

  // compute the fixpoint
  interval_widening_thresholdst interval_widening_thresholds;
  interval_map_domaint interval_domain(interval_widening_thresholds);
 
  typedef fixpointt<interval_mapt, concrete_transformert> interval_fixpointt;

  // compute fixpoint
  interval_fixpointt fix(transformers.transformers, interval_domain);
  
  interval_fixpointt::resultt fixpoint;
  
  interval_domain.initialise(fixpoint, transformers);
 
  fix.analyze(fixpoint, 3, 3); 

  fix.output(status(), fixpoint);
  // end of interval computation
  */
  

  //analyze
  //ssa_analyzert analyzer();
  //analyzer(nodes);
  summaryt summary;
  summary.params = functions[function_name]->params;
  summary.returns = functions[function_name]->returns;
  summary.globals_in = functions[function_name]->globals_in;
  summary.globals_out = functions[function_name]->globals_out;
  summary.precondition = preconditions.at(function_name);
  summary.transformer = true_exprt(); //analyzer.get_result(); //TODO

  out.clear();
  out << std::endl << "Summary for function " << function_name << std::endl;
  summary.output(out,functions[function_name]->ns);   
  debug() << out.str() << eom;

  summary_store.put(function_name,summary);
}

/*******************************************************************\

Function: summarizert::inline_summaries()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarizert::inline_summaries(const function_namet &function_name, 
  local_SSAt::nodest &nodes, bool recursive)
{
  ssa_inlinert inliner;
  // replace calls with summaries
  // TODO: functions with pointers passed as parameters
  for(local_SSAt::nodest::iterator n = nodes.begin(); n!=nodes.end(); n++)
  {
    for(local_SSAt::nodet::equalitiest::iterator e = n->second.equalities.begin();
        e != n->second.equalities.end(); e++)
    {
      if(e->rhs().id() != ID_function_application) continue;

      function_application_exprt f = to_function_application_expr(e->rhs());
      assert(f.function().id()==ID_symbol); //no function pointers
      irep_idt fname = to_symbol_expr(f.function()).get_identifier();
      summaryt summary; 
      bool recompute = false;
      // replace call with summary if it exists 
      if(summary_store.exists(fname)) 
      {
        status() << "Using existing summary for function " << fname << eom;
	summary = summary_store.get(fname);
	  //TODO: check whether summary applies (as soon as context-sensitive)
	  //      (requires retrieving the local context from the current analysis), 
	  //      otherwise compute new one: recompute = true;
      }
      // compute summary if function_name in functions
      else if(functions.find(fname)!=functions.end() && recursive) recompute = true;
      else // havoc function call by default
      {
        status() << "Function " << fname << " not found" << eom;
        inliner.havoc(n->second,e);
        continue;
      }
      if(recompute) 
      {
        status() << "Recursively summarizing function " << fname << eom;
        compute_summary_rec(fname);
        summary = summary_store.get(fname);
      }

      status() << "Replacing function " << fname << eom;
      //getting globals at call site
      local_SSAt::var_sett globals; 
      functions[function_name]->get_globals(n->first,globals);

#if DEBUG
      std::cout << "globals at call site: ";
      for(summaryt::var_sett::const_iterator it = globals.begin();
          it != globals.end(); it++)
         std::cout << from_expr(functions[function_name]->ns,"",*it) << " ";
      std::cout << std::endl;
#endif

      //replace
      inliner.replace(nodes,n,e,globals,summary);
    }
    inliner.commit_node(n);
  }
  inliner.commit_nodes(nodes);
}
