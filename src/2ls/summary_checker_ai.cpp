/*******************************************************************\

Module: Summary Checker for AI

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Summary Checker for AI

#include "summary_checker_ai.h"
#include <ssa/ssa_build_goto_trace.h>

property_checkert::resultt summary_checker_ait::operator()(
  const goto_modelt &goto_model)
{
  SSA_functions(goto_model, goto_model.symbol_table);

  ssa_unwinder.init(false, false);

  unsigned unwind=options.get_unsigned_int_option("unwind");
  if(unwind>0)
  {
    status() << "Unwinding" << messaget::eom;

    ssa_unwinder.init_localunwinders();

    ssa_unwinder.unwind_all(unwind);
  }

  // properties
  initialize_property_map(goto_model.goto_functions);

  property_checkert::resultt result=property_checkert::resultt::UNKNOWN;
  bool finished=false;
  while(!finished)
  {
    bool preconditions=options.get_bool_option("preconditions");
    bool termination=options.get_bool_option("termination");
    bool trivial_domain=options.get_bool_option("havoc");
    if(!trivial_domain || termination)
    {
      // forward analysis
      summarize(goto_model, true, termination);
    }
    if(!trivial_domain && preconditions)
    {
      // backward analysis
      summarize(goto_model, false, termination);
    }

    if(preconditions)
    {
      report_statistics();
      report_preconditions();
      return property_checkert::resultt::UNKNOWN;
    }

    if(termination)
    {
      report_statistics();
      return report_termination();
    }

#ifdef SHOW_CALLINGCONTEXTS
    if(options.get_bool_option("show-calling-contexts"))
      return property_checkert::resultt::UNKNOWN;
#endif

    result=check_properties();
    report_statistics();

    if(result==property_checkert::resultt::UNKNOWN &&
       options.get_bool_option("values-refine") &&
       options.get_bool_option("intervals"))
    {
      summary_db.clear();
      options.set_option("intervals", false);
      options.set_option("zones", true);
    }
    else
    {
      finished=true;
    }
  }
  return result;
}


void summary_checker_ait::report_preconditions()
{
  result() << eom;
  result() << "** " << (options.get_bool_option("sufficient") ?
      "Sufficient" : "Necessary")
     << " preconditions: " << eom;
  ssa_dbt::functionst &functions=ssa_db.functions();
  for(ssa_dbt::functionst::iterator it=functions.begin();
      it!=functions.end(); it++)
  {
    exprt precondition;
    bool computed=summary_db.exists(it->first);
    if(computed)
      precondition=summary_db.get(it->first).bw_precondition;
    if(precondition.is_nil())
      computed=false;
    result() << eom << "[" << it->first << "]: " <<
      (!computed?"not computed":from_expr(it->second->ns, "", precondition))
             << eom;
  }
}

property_checkert::resultt summary_checker_ait::report_termination()
{
  result() << eom;
  result() << "** Termination: " << eom;
  bool not_computed=true;
  bool all_terminate=true;
  bool one_nonterminate=false;
  ssa_dbt::functionst &functions=ssa_db.functions();
  for(ssa_dbt::functionst::iterator it=functions.begin();
      it!=functions.end(); it++)
  {
    threevalt terminates=YES;
    bool computed=summary_db.exists(it->first);
    if(computed)
    {
      terminates=summary_db.get(it->first).terminates;
      not_computed=false;
    }
    all_terminate=all_terminate && (terminates==YES);
    one_nonterminate=one_nonterminate || (terminates==NO);
    result() << "[" << it->first << "]: "
       << (!computed ? "not computed" : threeval2string(terminates)) << eom;
  }
  if(not_computed)
    return property_checkert::resultt::UNKNOWN;
  if(all_terminate)
    return property_checkert::resultt::PASS;
  if(one_nonterminate)
  {
#if 0
    return property_checkert::resultt::FAIL;
#else
    // rely on nontermination checker to find counterexample
    return property_checkert::resultt::UNKNOWN;
#endif
  }
  return property_checkert::resultt::UNKNOWN;
}
