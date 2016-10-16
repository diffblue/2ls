/*******************************************************************\

Module: Template Generator for Recursive Summaries

Author: Peter Schrammel

\*******************************************************************/

#define SHOW_TEMPLATE

#include "template_generator_recsum.h"
#include "equality_domain.h"
#include "tpolyhedra_domain.h"

#include <util/find_symbols.h>
#include <util/arith_tools.h>
#include <util/simplify_expr.h>
#include <util/mp_arith.h>

#include <ssa/ssa_inliner.h>

#ifdef DEBUG
#include <iostream>
#endif

/*******************************************************************\

Function: template_generator_recsumt::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void template_generator_recsumt::operator()(unsigned _domain_number, 
			  const local_SSAt &SSA,  bool forward)
{
  domain_number = _domain_number;
  handle_special_functions(SSA); // we have to call that to prevent trouble!

  // do not compute summary for entry-point
  if(SSA.goto_function.body.instructions.front().function!=ID__start ||
     options.get_bool_option("preconditions"))
  {
    collect_variables_in(var_specs, SSA, forward);
    collect_variables_out(var_specs, SSA, forward);
    collect_variables_rec(SSA);
  }

  // either use standard templates or user-supplied ones
  if(!instantiate_custom_templates(var_specs,SSA))
    instantiate_standard_domains(var_specs,SSA);

#ifdef SHOW_TEMPLATE
  debug() << "Template: " << eom;
  domain_ptr->output_domain(debug(), SSA.ns); debug() << eom;
#endif  
}

/*******************************************************************\

Function: template_generator_recsumt::collect_variables_rec

  Inputs:

 Outputs:

 Purpose: builds Loop(xin,xpout), Loop(xpin,xout) predicates

\*******************************************************************/

void template_generator_recsumt::collect_variables_rec(
  const local_SSAt &SSA)
{
  //guard of inputs
  exprt guard_in = 
    SSA.guard_symbol(SSA.goto_function.body.instructions.begin());

  //guard of outputs
  exprt guard_out = 
    SSA.guard_symbol(--SSA.goto_function.body.instructions.end());

  //collect recursive function calls
  for(local_SSAt::nodest::const_iterator n_it = SSA.nodes.begin();
      n_it != SSA.nodes.end(); n_it++)
  {
    for(local_SSAt::nodet::function_callst::const_iterator f_it = 
	  n_it->function_calls.begin();
        f_it != n_it->function_calls.end(); f_it++)
    {
      //is it a recursive function call?
    	irep_idt fname = to_symbol_expr(f_it->function()).get_identifier();
      if(SSA.goto_function.body.instructions.front().function!=fname)
        continue;

      //get guard of call site
      //TODO: these are not the same for backward analysis
      exprt guard_cs_in = SSA.guard_symbol(n_it->location);
      exprt guard_cs_out = SSA.cond_symbol(n_it->location);

      //add function arguments
      assert(f_it->arguments().size()==SSA.params.size());
      for(size_t i=0; i<SSA.params.size(); ++i)
      {
        symbol_exprt arg=to_symbol_expr(f_it->arguments()[i]);
        post_renaming_map[SSA.params[i]]=arg;
        add_var(SSA.params[i],guard_in,guard_cs_in,domaint::LOOP,var_specs);
      }

      //get input globals at call site
      local_SSAt::var_sett cs_globals_in;
      SSA.get_globals(n_it->location,cs_globals_in,true,false); //filters out return values
      for(local_SSAt::var_sett::iterator v_it = cs_globals_in.begin();
          v_it != cs_globals_in.end(); v_it++)
      {
        symbol_exprt symbol;
        if(ssa_inlinert::find_corresponding_symbol(*v_it,SSA.globals_in,symbol))
        {
          post_renaming_map[symbol]=*v_it;
          add_var(symbol,guard_in,guard_cs_in,
                  domaint::LOOP,
                  var_specs);
        }
      }

      //get output globals at call site
      local_SSAt::var_sett cs_globals_out;
      SSA.get_globals(n_it->location,cs_globals_out,false,true,fname); //with return values for function call
      for(local_SSAt::var_sett::iterator v_it = cs_globals_out.begin();
          v_it != cs_globals_out.end(); v_it++)
      {
        symbol_exprt symbol;
        if(ssa_inlinert::find_corresponding_symbol(*v_it,SSA.globals_out,symbol))
        {
          post_renaming_map[*v_it]=symbol;
          add_var(*v_it,guard_cs_out,guard_out,
                  domaint::LOOP,
                  var_specs);
        }
      }

    }
  }
}

/*******************************************************************\

Function: template_generator_recsumt::inout_vars

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

domaint::var_sett template_generator_recsumt::inout_vars()
{
  domaint::var_sett vars;
  for(domaint::var_specst::const_iterator v = var_specs.begin(); 
      v!=var_specs.end(); v++)
  {
    if(v->kind==domaint::IN || v->kind==domaint::OUT) vars.insert(v->var);
  }
  return vars;
}
