/*******************************************************************\

Module: Storage for Function SSAs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_LOCAL_SSA_DB_H
#define CPROVER_LOCAL_SSA_DB_H

#include "../ssa/local_ssa.h"
#include <goto-programs/goto_functions.h>

class ssa_dbt
{
public:
  typedef irep_idt function_namet;
  typedef std::map<function_namet, local_SSAt*> functionst;

  ~ssa_dbt() 
  {
    for(functionst::iterator it = store.begin();
        it != store.end(); it++)
      delete it->second;
  }

  local_SSAt &get(const function_namet &function_name) const 
    { return *store.at(function_name); }

  functionst &functions() { return store; }

  bool exists(const function_namet &function_name) const  
    { return store.find(function_name)!=store.end(); }

  void create(const function_namet &function_name, 
              const goto_functionst::goto_functiont &goto_function,
              const namespacet &ns) 
  { 
    store[function_name] = new local_SSAt(goto_function,ns);
  }

 protected:
  functionst store;
};

#endif
