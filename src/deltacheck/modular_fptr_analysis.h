/*******************************************************************\

Module: Modular (i.e., per C file) analysis of function pointers.

Author: Ondrej Sery, ondrej.sery@d3s.mff.cuni.cz

\*******************************************************************/

#ifndef CPROVER_DELTACHECK_MODULAR_FPTR_ANALYSIS_H
#define	CPROVER_DELTACHECK_MODULAR_FPTR_ANALYSIS_H

#include "modular_code_analysis.h"

class modular_fptr_analysist : public modular_code_analysist {
public:
  modular_fptr_analysist();
  virtual ~modular_fptr_analysist();
  
  virtual const char* get_default_suffix() const
  {
    return ".dc_fp";
  }
  virtual const char* get_analysis_id() const
  {
    return "Function pointer analysis";
  }
  
  virtual void enter_function(const irep_idt& function_id)
  { 
    current_function = function_id;
  }
  virtual void exit_function() {};
  
  virtual void accept_assign(const code_assignt& instruction);
  virtual void accept_function_call(const code_function_callt& instruction);
  
  // Analysis relevant functions
  virtual bool try_compute_value(const exprt& expr, valuet& value);
  virtual bool try_compute_variable(const exprt& expr, variablet& variable);
  
private:
  irep_idt current_function;
};

#endif

