/*******************************************************************\

Module: Summarizer

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "../ssa/local_ssa.h"
#include "../ssa/simplify_ssa.h"

#include "function_signature.h"
#include "summary_db.h"
#include "summarizer.h"

/*******************************************************************\

Function: summarizert::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarizert::operator()(const goto_modelt &goto_model)
{
  // analyze all the functions
  forall_goto_functions(f_it, goto_model.goto_functions)
    summarize(goto_model, f_it);
}

/*******************************************************************\

Function: summarizert::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarizert::operator()(
  const goto_modelt &goto_model,
  const irep_idt &id)
{
  // analyze the given function only

  goto_functionst::function_mapt::const_iterator f_it=
    goto_model.goto_functions.function_map.find(id);
  
  if(f_it==goto_model.goto_functions.function_map.end())
    throw "function not found";

  summarize(goto_model, f_it);
}

/*******************************************************************\

Function: summarizert::summarize

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarizert::summarize(
  const goto_modelt &goto_model,
  const goto_functionst::function_mapt::const_iterator f_it)
{
  status() << "** Analyzing " << f_it->first << messaget::eom;
    
  summary_dbt summary_db;
  
  summary_db.set_message_handler(get_message_handler());
  summary_db.read(id2string(f_it->first));

  const namespacet ns(goto_model.symbol_table);
  
  // build SSA
  progress() << "Building SSA" << messaget::eom;
  local_SSAt SSA(f_it->second, ns);
  
  // simplify, if requested
  if(simplify)
  {
    progress() << "Simplifying" << messaget::eom;
    ::simplify(SSA, ns);
  }

  
  // fixed-point for loops
  #if 0
  progress() << "Fixed-point" << messaget::eom;
  ssa_fixed_point(SSA);
  #endif

  update_function_signature(SSA, summary_db.summary);
  
  summary_db.write();
}

/*******************************************************************\

Function: summarizert::report_statistics()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarizert::report_statistics()
{
}
  
