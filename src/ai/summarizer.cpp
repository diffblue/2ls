#include <iostream>


#include "summarizer.h"
#include "summary_store.h"

summaryt summarizert::summarize(const functiont &function, const preconditiont &precondition)
{
  functions.clear();
  preconditions.clear();
  functions[function.first] = function.second;
  preconditions[function.first] = precondition; 
  run();
  return summary_store.get(function.first);
}

summaryt summarizert::summarize(const functiont &function)
{ 
  return summarize(function,true_exprt()); 
} 

void summarizert::summarize(const functionst &_functions)
{
  preconditionst _preconditions;
  for(functionst::const_iterator it = _functions.begin(); it!=_functions.end(); it++)
  {
    _preconditions[it->first] = true_exprt();
  }
  summarize(_functions,_preconditions);
}

void summarizert::summarize(const functionst &_functions,const preconditionst &_preconditions)
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
    std::cout << "Summarizing function " << it->first << std::endl;
    if(!summary_store.exists(it->first)) compute_summary_rec(it->first);
    else std::cout << "Summary for function " << it->first << " exists already" << std::endl;
  }
}

void summarizert::compute_summary_rec(function_namet function_name)
{
  local_SSAt::nodest nodes = functions[function_name]->nodes; //copy nodes

  // replace calls with summaries
  for(local_SSAt::nodest::iterator n = nodes.begin(); n!=nodes.end(); n++)
  {
    local_SSAt::nodet::equalitiest new_equs;
    std::set<local_SSAt::nodet::equalitiest::iterator> rm_equs;
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
        std::cout << "Using existing summary for function " << fname << std::endl;
	summary = summary_store.get(fname);
	  //TODO: check whether summary applies (as soon as context-sensitive)
	  //      (requires retrieving the local context from the current analysis), 
	  //      otherwise compute new one: recompute = true;
      }
      // compute summary if function_name in functions
      else if(functions.find(fname)!=functions.end()) recompute = true;
      else // havoc function call by default
      {
        std::cout << "Function " << fname << " not found" << std::endl;
        rm_equs.insert(e);
        continue;
      }
      if(recompute) 
      {
        std::cout << "Recursively summarizing function " << fname << std::endl;
        compute_summary_rec(fname);
        summary = summary_store.get(fname);
      }
      //replace
      std::cout << "Inlining summary for " << fname << std::endl;
      //TODO: need some renaming
      n->second.constraints.push_back(summary.transformer);
      //constraints for return values
      exprt::operandst retvals;
      retvals.reserve(summary.exit_vars.size());
      for(summaryt::var_listt::const_iterator it3 = summary.exit_vars.begin();
          it3 != summary.exit_vars.end(); it3++)
      {
        retvals.push_back(equal_exprt(e->lhs(),*it3));
      }
      n->second.constraints.push_back(disjunction(retvals));
      rm_equs.insert(e);
      //equalities for arguments
      summaryt::var_listt::const_iterator it1 = summary.entry_vars.begin();
      for(exprt::operandst::const_iterator it2 = f.arguments().begin();
          it2 != f.arguments().end(); it2++, it1++)
      {
        assert(it1!=summary.entry_vars.end());
        new_equs.push_back(equal_exprt(*it1,*it2));
      }
    }
    //remove obsolete equalities
    for(std::set<local_SSAt::nodet::equalitiest::iterator>::iterator it = rm_equs.begin();
	it != rm_equs.end(); it++) n->second.equalities.erase(*it);
    //insert new equalities
    n->second.equalities.insert(n->second.equalities.end(),new_equs.begin(),new_equs.end());
  }

  std::cout << "function to be analyzed: " << std::endl;
  for(local_SSAt::nodest::iterator n = nodes.begin(); n!=nodes.end(); n++)
    if(!n->second.empty()) n->second.output(std::cout,functions[function_name]->ns);

  //analyze
  //TODO
  // analyzer.analyze(nodes);
  summaryt summary;
  summary.entry_vars = functions[function_name]->entry_vars;
  summary.exit_vars = functions[function_name]->exit_vars;
  summary.precondition = preconditions.at(function_name);
  summary.transformer = true_exprt(); //analyzer.get_result(); //TODO
  summary_store.put(function_name,summary);
}

