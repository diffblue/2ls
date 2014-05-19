#include "summarizer.h"

summaryt summarizert::summarize(functiont function, preconditiont precondition)
{
  functions.clear();
  preconditions.clear();
  functions[function.first] = function.second;
  preconditions[function.first] = precondition;
  run();
  return summary_store.get(function.first);
}

summaryt summarizert::summarize(functiont function)
{ 
  return summarize(function,true_exprt()); 
} 

void summarizert::summarize(functionst _functions);
{
  preconditionst _preconditions;
  for(functionst::const_iterator it = _functions.begin(); it!=_functions.end(); it++)
  {
    _preconditions[it->first] = true_exprt();
  }
  summarize(_functions,_preconditions);
}

void summarizert::summarize(functionst _functions, preconditionst _preconditions);
{
  functions = _functions;
  preconditions = _preconditions;
  run();
}

void summarizer::run()
{
  //TODO: compute fixed point (if any descendents in the call graph are updated)
  //TODO: make context sensitive (currently, only globally given preconditions are used)
  //TODO: replace simple iterator by something following the call graph
  for(functionst::const_iterator it = _functions.begin(); it!=_functions.end(); it++)
  {
     if(!summary_store.exists(it->first)) compute_summary_rec(it->first);
  }
}

void summarizer::compute_summary_rec(function_namet function_name)
{
  function_bodyt body = functions[function_name];

  // replace calls with summaries
  for( it )
  {
    summaryt summary = true_exprt(); // havoc function call by default
    bool recompute = false;
    // replace call with summary if it exists 
    if(summary_store.exists(*it)) 
    {
      summary = summary_store.get(*it);
      //TODO: check whether summary applies (as soon as context-sensitive)
      //      (requires retrieving the local context from the current analysis), 
      //      otherwise compute new one: recompute = true;
    }
    // compute summary if function_name in functions
    else if(functions.find(*it)!=functions.end()) recompute = true;
    
    if(recompute) 
    {
      compute_summary_rec(*it);
      summary = summary_store.get(*it);
    }
    //replace
    //TODO
  }

  //analyze
  //TODO
  analyzer.analyze();
  summaryt summary;
  //summary.entry_vars = ; //TODO
  //summary.exit_vars = ; //TODO
  summary.precondition = preconditions[function_name];
  summary.transformer = analyzer.get_result(); //TODO
  summary_store.put(function_name,summary);
}

