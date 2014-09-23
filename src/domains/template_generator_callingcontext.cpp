/*******************************************************************\

Module: Template Generator for Calling Contexts

Author: Peter Schrammel

\*******************************************************************/

#include "template_generator_callingcontext.h"

#include <util/find_symbols.h>

/*******************************************************************\

Function: template_generator_callingcontextt::collect_variables_callingcontext

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void template_generator_callingcontextt::collect_variables_callingcontext(
  local_SSAt &SSA,    
  local_SSAt::nodest::iterator n_it,
  local_SSAt::nodet::function_callst::iterator f_it,
  bool forward)
{
  exprt guard = SSA.guard_symbol(n_it->location);

  //getting globals at call site
  local_SSAt::var_sett cs_globals_in;
  if(forward)
  {
    SSA.get_globals(n_it->location,cs_globals_in,false,false); //filter out return values
  }
  else
  {
    local_SSAt::nodest::iterator nnext = n_it; nnext++;
    SSA.get_globals(nnext->location,cs_globals_in,true,true); //with return values
  }

  for(local_SSAt::var_sett::iterator v_it = cs_globals_in.begin();
      v_it != cs_globals_in.end(); v_it++)
  {
    if(SSA.globals_in.find(*v_it)!=SSA.globals_in.end())
      add_var(*v_it,guard,guard,
	      domaint::OUT, //the same for both forward and backward
	      var_specs);
  }

  //add function arguments
  if(!forward) return; // nothing to do
  for(exprt::operandst::const_iterator a_it =  f_it->arguments().begin();
      a_it !=  f_it->arguments().end(); a_it++)
  {
    std::set<symbol_exprt> args;
    find_symbols(*a_it,args); 
    add_vars(args,guard,guard,domaint::OUT,var_specs);
  }

}

/*******************************************************************\

Function: template_generator_callingcontextt::callingcontext_vars

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

domaint::var_sett template_generator_callingcontextt::callingcontext_vars()
{
  domaint::var_sett vars;
  for(domaint::var_specst::const_iterator v = var_specs.begin(); 
      v!=var_specs.end(); v++)
  {
    if(v->kind==domaint::OUT) vars.insert(v->var);
  }
  return vars;
}
