/*******************************************************************\

Module: Storage for Function SSAs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_LOCAL_SSA_DB_H
#define CPROVER_LOCAL_SSA_DB_H

#include <util/options.h>

#include "../ssa/local_ssa.h"
#include "../ssa/ssa_unwinder2.h"
#include "../domains/incremental_solver.h"
#include <goto-programs/goto_functions.h>

class ssa_dbt
{
public:
  typedef irep_idt function_namet;
  typedef std::map<function_namet, ssa_local_unwinder2t*> functionst;
  typedef std::map<function_namet, incremental_solvert*> solverst;

  explicit ssa_dbt(const optionst &_options) 
    : options(_options)
    { }
  
  ~ssa_dbt() 
  {
    for(functionst::iterator it = store.begin();
        it != store.end(); it++)
      delete it->second;
    for(solverst::iterator it = the_solvers.begin();
        it != the_solvers.end(); it++)
      delete it->second;
  }

  local_SSAt &get(const function_namet &function_name) const 
    { return *store.at(function_name); }

  incremental_solvert &get_solver(const function_namet &function_name)
  { 
    solverst::iterator it = the_solvers.find(function_name);
    if(it!=the_solvers.end()) return *(it->second);
    the_solvers[function_name] = 
      incremental_solvert::allocate(store.at(function_name)->ns,
				    options.get_bool_option("refine"));
    return *the_solvers.at(function_name); 
  }

  functionst &functions() { return store; }
  solverst &solvers() { return the_solvers; }

  bool exists(const function_namet &function_name) const  
    { return store.find(function_name)!=store.end(); }

  void create(const function_namet &function_name, 
              const goto_functionst::goto_functiont &goto_function,
              const namespacet &ns) 
  { 
    store[function_name] = new ssa_local_unwinder2t(goto_function,ns);
  }

 protected:
  const optionst &options;
  functionst store;
  solverst the_solvers;
};

#endif
