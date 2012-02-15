/*******************************************************************\

Module: The ancestor of modular (i.e., per C file) fixpoint analysis 
of goto-programs. Based on partial_analysist, this class adds visitor-like
processing of goto-programs.

The class supports serialization and deserialization to/from a text file.
Multiple deserialization results in merged rules, which is useful to merge 
results of the analysis of different individual modules. After such merging,
fixpoint computation should be run to obtain the result of the overall analysis.

Author: Ondrej Sery, ondrej.sery@d3s.mff.cuni.cz

\*******************************************************************/

#ifndef CPROVER_DELTACHECK_MODULAR_CODE_ANALYSIS_H
#define	CPROVER_DELTACHECK_MODULAR_CODE_ANALYSIS_H

#include <goto-programs/goto_program.h>
#include <irep.h>
#include "modular_analysis.h"

class modular_code_analysist : public modular_analysist<irep_idt, irep_idt,
        irep_id_hash, irep_id_hash> {
public:
  modular_code_analysist();
  virtual ~modular_code_analysist();
  
  virtual const char* get_default_suffix() const = 0;
  virtual const char* get_analysis_id() const = 0;
  
  // Instruction visitor functions
  void visit(const goto_programt::instructiont& instr);
  virtual void enter_function(const irep_idt& function_id) {}
  virtual void exit_function() {};
  
  virtual void accept_assume(const code_assumet& instruction) {};
  virtual void accept_assign(const code_assignt& instruction) {};
  virtual void accept_assert(const code_assertt& instruction) {};
  virtual void accept_function_call(const code_function_callt& instruction) {};
  virtual void accept_return(const code_returnt& instruction) {};
  
  // Analysis relevant functions
  virtual bool try_compute_value(const exprt& expr, valuet& value) = 0;
  virtual bool try_compute_variable(const exprt& expr, variablet& variable) = 0;
  
  virtual void print(std::ostream& out) const;
  virtual void serialize(std::ostream& out) const;
  virtual void deserialize(std::istream& in);
};

#endif

