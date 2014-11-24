/*******************************************************************\

Module: Storage for Function Summaries

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "summary_db.h"

void summary_dbt::put(const function_namet &function_name, const summaryt &summary)
{ 
  if(store.find(function_name)==store.end() || store[function_name].mark_recompute)
    store[function_name] = summary; 
  else
    store[function_name].join(summary);
}

void summary_dbt::mark_recompute_all()
{
  for(std::map<function_namet, summaryt>::iterator it = store.begin();
      it != store.end(); it++)
    it->second.mark_recompute = true;
}
