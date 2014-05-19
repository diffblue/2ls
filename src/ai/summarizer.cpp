#include "summarizer.h"
#include "summary_store.h"

summaryt summarizert::summarize(functiont function, preconditiont precondition)
{
  functions.clear();
  preconditions.clear();
  //  functions[function.first] = function.second; //TODO
  preconditions[function.first] = precondition;
  run();
  return summary_store.get(function.first);
}

summaryt summarizert::summarize(functiont function)
{ 
  return summarize(function,predicatet(true_exprt())); 
} 

void summarizert::summarize(functionst _functions)
{
  preconditionst _preconditions;
  for(functionst::const_iterator it = _functions.begin(); it!=_functions.end(); it++)
  {
    _preconditions[it->first] = true_exprt();
  }
  summarize(_functions,_preconditions);
}

void summarizert::summarize(functionst _functions, preconditionst _preconditions)
{
  functions = _functions;
  preconditions = _preconditions;
  run();
}

void summarizert::run()
{
  //TODO: compute fixed point (if any descendents in the call graph are updated)
  //TODO: make context sensitive (currently, only globally given preconditions are used)
  //TODO: replace simple iterator by something following the call graph
  for(functionst::const_iterator it = functions.begin(); it!=functions.end(); it++)
  {
     if(!summary_store.exists(it->first)) compute_summary_rec(it->first);
  }
}

void summarizert::compute_summary_rec(function_namet function_name)
{
  function_bodyt &body = functions.at(function_name); //TODO: must copy here

  // replace calls with summaries
  for(local_SSAt::nodest::iterator n = body.nodes.begin(); n!=body.nodes.end(); n++)
  {
    for(local_SSAt::nodet::equalitiest::iterator e = n->second.equalities.begin();
        e != n->second.equalities.begin(); e++)
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
	  summary = summary_store.get(fname);
	  //TODO: check whether summary applies (as soon as context-sensitive)
	  //      (requires retrieving the local context from the current analysis), 
	  //      otherwise compute new one: recompute = true;
	}
      // compute summary if function_name in functions
      else if(functions.find(fname)!=functions.end()) recompute = true;
      else // havoc function call by default
      {
        *e = equal_exprt(true_exprt(),true_exprt()); //TODO
        continue;
      }
      if(recompute) 
      {
        compute_summary_rec(fname);
        summary = summary_store.get(fname);
      }
      //replace
      //TODO: need some renaming
      function_bodyt &fbody = functions.at(fname);
      n->second.constraints.push_back(summary.transformer);
      //remove equality      
      *e = equal_exprt(true_exprt(),true_exprt()); //TODO
      //equalities for arguments
      summaryt::var_listt::const_iterator it1 = fbody.entry_vars.begin();
      for(exprt::operandst::const_iterator it2 = f.arguments().begin();
          it2 != f.arguments().end(); it2++, it1++)
      {
        assert(it1!=body.entry_vars.end());
        n->second.equalities.push_back(equal_exprt(*it1,*it2));
      }
      //constraints for return values
      exprt::operandst retvals;
      for(summaryt::var_listt::const_iterator it2 = fbody.exit_vars.begin();
          it2 != fbody.exit_vars.end(); it2++)
      {
        retvals.push_back(equal_exprt(e->lhs(),*it2));
      }
      n->second.constraints.push_back(disjunction(retvals));
    }
  }

  //analyze
  //TODO
  // analyzer.analyze();
  summaryt summary;
  summary.entry_vars = body.entry_vars;
  summary.exit_vars = body.exit_vars;
  summary.precondition = preconditions[function_name];
  //summary.transformer = analyzer.get_result(); //TODO
  summary_store.put(function_name,summary);
}

