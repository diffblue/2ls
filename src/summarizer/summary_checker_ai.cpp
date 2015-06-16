/*******************************************************************\

Module: Summary Checker for AI

Author: Peter Schrammel

\*******************************************************************/

#include "summary_checker_ai.h"

/*******************************************************************\

Function: summary_checker_ait::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

property_checkert::resultt summary_checker_ait::operator()(
  const goto_modelt &goto_model)
{
  const namespacet ns(goto_model.symbol_table);

  SSA_functions(goto_model,ns);

  ssa_unwinder.init(false,false);

  unsigned unwind = options.get_unsigned_int_option("unwind");
  if(unwind>0)
  {
    status() << "Unwinding" << messaget::eom;

    ssa_unwinder.init_localunwinders();

    ssa_unwinder.unwind_all(unwind+1);
    ssa_unwinder.output(debug()); debug() <<eom;
  }

  // properties
  initialize_property_map(goto_model.goto_functions);

  bool preconditions = options.get_bool_option("preconditions");
  if(!options.get_bool_option("havoc")) 
  {
    //forward analysis
    summarize(goto_model,true,false);
  }
  if(!options.get_bool_option("havoc") && preconditions)
  {
    //backward analysis
    summarize(goto_model,false,false);
  }

  if(preconditions) 
  {
    report_statistics();
    report_preconditions();
    return property_checkert::UNKNOWN;
  }

#ifdef SHOW_CALLINGCONTEXTS
  if(options.get_bool_option("show-calling-contexts"))
    return property_checkert::UNKNOWN;
#endif

  property_checkert::resultt result =  check_properties(); 
  report_statistics();
  return result;
}


/*******************************************************************\

Function: summary_checker_ait::report_preconditions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summary_checker_ait::report_preconditions()
{
  result() << eom;
  result() << "** " << (options.get_bool_option("sufficient") ? 
			"Sufficient" : "Necessary")
	   << " preconditions: " << eom;
  ssa_dbt::functionst &functions = ssa_db.functions();
  for(ssa_dbt::functionst::iterator it = functions.begin();
      it != functions.end(); it++)
  {
    exprt precondition;
    bool computed = summary_db.exists(it->first);
    if(computed) precondition = summary_db.get(it->first).bw_precondition;
    if(precondition.is_nil()) computed = false;
    result() << eom << "[" << it->first << "]: " 
	     << (!computed ? "not computed" : 
		 from_expr(it->second->ns, "", precondition)) << eom;
  }
}
