/*******************************************************************\

Module: Modular (i.e., per C file) analysis of function pointers.

The aliasing data is assigned to the following entities with decreasing 
priority:
- symbol (variable, variable.field, function)
- fields of structures (i.e., shared among structures of the same type)
- types (i.e., specific type of function pointer)
- wildcard (matches anything unknown)

FIXME: The following is not addressed at all:
- function parameters, return value
- non-scalar assignment: structures, arrays

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

  // Queries for the call graph
  bool get_callees(const irep_idt& function, valuest& functions);
  
protected:
  virtual void accept_assign(const code_assignt& instruction);
  virtual void accept_function_call(const code_function_callt& instruction);
  virtual void accept_return(const code_returnt& instruction);
  
private:
  irep_idt any_variable;
  
  void process_assignment(const variablet& lhs_var, const exprt& rhs);
  
  bool try_compute_symbol_variable(const exprt& expr, variablet& variable);
  bool try_compute_field_access_variable(const exprt& expr, variablet& variable);
  bool try_compute_type_variable(const exprt& expr, variablet& variable);
  
  bool try_compute_constant_value(const exprt& expr, valuet& value);
  bool try_compute_variable(const exprt& expr, variablet& variable);
  
  bool is_symbol_visible(const symbolt& symbol);
};

#endif

