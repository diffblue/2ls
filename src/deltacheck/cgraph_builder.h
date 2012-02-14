/*******************************************************************\

Module: Call graph builder, builds and stores partial call graphs
(per C file).

Author: Ondrej Sery, ondrej.sery@d3s.mff.cuni.cz

\*******************************************************************/

#ifndef CPROVER_DELTACHECK_CGRAPH_BUILDER_H
#define	CPROVER_DELTACHECK_CGRAPH_BUILDER_H

#include <goto-programs/goto_functions.h>
#include <goto-programs/goto_program.h>
#include <irep.h>

#include "partial_analysis.h"

class cgraph_buildert {
public:
  cgraph_buildert();
  
  void analyze_module(const goto_functionst& functions);
  void analyze_function(
          irep_idt current_function,
          const goto_functionst::goto_functiont& function);
  void analyze_instruction(
          irep_idt current_function,
          const goto_programt::instructiont& instr);
  void analyze_function_call(
          irep_idt current_function,
          const code_function_callt& function_call);
  void analyze_assignment(const code_assignt& assignment);
  
private:

  irep_idt compute_variable_name(const exprt& expr);
  partial_analysist<irep_idt, irep_idt, irep_id_hash, irep_id_hash> 
          partial_analysis;
};

#endif

