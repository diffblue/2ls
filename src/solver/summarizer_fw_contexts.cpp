/*******************************************************************\

Module: Summarizer for Forward Analysis with Calling Context output

Author: Peter Schrammel

\*******************************************************************/

#include <iostream>

#include <util/simplify_expr.h>
#include <solvers/sat/satcheck.h>
#include <solvers/flattening/bv_pointers.h>
#include <solvers/smt2/smt2_dec.h>
#include <util/find_symbols.h>

#include <util/xml.h>
#include <util/xml_expr.h>
#include <util/i2string.h>

#include "summarizer_fw_contexts.h"
#include "summary_db.h"

#include "../domains/ssa_analyzer.h"
#include "../domains/template_generator_summary.h"
#include "../domains/template_generator_callingcontext.h"

#include "../ssa/local_ssa.h"
#include "../ssa/simplify_ssa.h"

/*******************************************************************\

Function: summarizer_fw_contextst::summarize()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarizer_fw_contextst::summarize()
{
  exprt precondition = true_exprt(); //initial calling context
  for(functionst::const_iterator it = ssa_db.functions().begin(); 
      it!=ssa_db.functions().end(); it++)
  {
    if(excluded_functions.find(it->first)!=excluded_functions.end())
      continue;
    status() << "\nSummarizing function " << it->first << eom;
    if(!summary_db.exists(it->first) || 
     summary_db.get(it->first).mark_recompute) 
      compute_summary_rec(it->first,precondition,false);
    else status() << "Summary for function " << it->first << 
           " exists already" << eom;
  }
}

/*******************************************************************\

Function: summarizer_fw_contextst::inline_summaries()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarizer_fw_contextst::inline_summaries(
                                   const function_namet &function_name, 
				   local_SSAt &SSA, const exprt &precondition,
				   bool context_sensitive)
{
  for(local_SSAt::nodest::const_iterator n_it = SSA.nodes.begin();
      n_it != SSA.nodes.end(); n_it++)
  {
    for(local_SSAt::nodet::function_callst::const_iterator f_it = 
	  n_it->function_calls.begin();
        f_it != n_it->function_calls.end(); f_it++)
    {
      assert(f_it->function().id()==ID_symbol); //no function pointers
      if(!check_call_reachable(function_name,SSA,n_it,f_it,precondition,true)) 
      {
	continue;
      }

      irep_idt fname = to_symbol_expr(f_it->function()).get_identifier();

      if(excluded_functions.find(fname)!=excluded_functions.end())
      {
	exprt precondition_call = compute_calling_context(
	    function_name,SSA,n_it,f_it,precondition,true);

	// output calling context
	switch(ui)
	{
	case ui_message_handlert::PLAIN:
	  break;
	  
	case ui_message_handlert::XML_UI:
	  {
	    xmlt xml_cc("calling-context");
	    xml_cc.set_attribute("function",id2string(fname));
	    xml_cc.set_attribute("goto_location",
			      i2string(n_it->location->location_number));

	    //location
	    const source_locationt &source_location =
	      n_it->location->source_location;
	    xmlt xml_location;
	    if(source_location.is_not_nil() && source_location.get_file()!="")
	      xml_location=xml(source_location);
	    if(xml_location.name!="")
	      xml_cc.new_element().swap(xml_location);

	    //argument ranges
	    xmlt xml_args("argument-ranges");
	    assert(precondition_call.operands().size()%2==0);
	    for(unsigned i=0;i<precondition_call.operands().size();i+=2)
	    {
              xmlt xml_arg("argument-range");
	      xmlt xml_lower("lower_expression");
	      xmlt xml_lower_value = 
		xml(precondition_call.operands()[i+1].op1(),SSA.ns);
	      xml_lower.new_element().swap(xml_lower_value);
	      xmlt xml_upper("upper_expression");
	      xmlt xml_upper_value = 
		xml(precondition_call.operands()[i].op1(),SSA.ns);
	      xml_upper.new_element().swap(xml_upper_value);
	      xml_arg.new_element().swap(xml_lower);
	      xml_arg.new_element().swap(xml_upper);
	      xml_args.new_element().swap(xml_arg);
	    }
	    xml_cc.new_element().swap(xml_args);
            std::cout << xml_cc << "\n";
	  }
	  break;
	default:
	  assert(false);
	}

	// put dummy summary
	const local_SSAt &SSA_call = ssa_db.get(fname);
	summaryt summary;
	summary.params = SSA_call.params;
	summary.globals_in = SSA_call.globals_in;
	summary.globals_out = SSA_call.globals_out;
	summary.fw_precondition = precondition_call;
	summary.fw_transformer = true_exprt();

        summary_db.put(fname,summary);
	continue;
      }

      if(!check_precondition(function_name,SSA,n_it,f_it,
			     precondition,context_sensitive))
      {
	exprt precondition_call = true_exprt();
	if(context_sensitive) 
	  precondition_call = compute_calling_context(
	    function_name,SSA,n_it,f_it,precondition,true);

	status() << "Recursively summarizing function " << fname << eom;
	compute_summary_rec(fname,precondition_call,context_sensitive);
	summaries_used++;
      }
    }
  }
}


