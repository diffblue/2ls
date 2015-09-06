/*******************************************************************\

Module: Instrument Goto Program with Inferred Information

Author: Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_INSTRUMENT_GOTO_H
#define CPROVER_INSTRUMENT_GOTO_H

#include <goto-programs/goto_model.h>
#include <util/options.h>

#include "../ssa/local_ssa.h"
#include "../ssa/ssa_unwinder.h"
#include "ssa_db.h"
#include "summary_db.h"

class instrument_gotot:public messaget
{
public:
  inline instrument_gotot(optionst &_options,
			  ssa_dbt &_ssa_db,
			  summary_dbt &_summary_db):
    options(_options),
    ssa_db(_ssa_db),summary_db(_summary_db)
  {
  }

  void operator()(goto_modelt &goto_model);

 protected:
  optionst &options;

  ssa_dbt &ssa_db;
  summary_dbt &summary_db;
  
  void instrument_function(
    const irep_idt &function_name,
    goto_functionst::goto_functiont &function);

  void instrument_body(
    const local_SSAt &SSA,
    const exprt &expr,
    goto_functionst::goto_functiont &function);

  void instrument_instruction(
    const exprt &expr,
    goto_programt &dest,
    goto_programt::targett &target);

};

#endif
