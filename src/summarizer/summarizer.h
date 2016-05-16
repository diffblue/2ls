/*******************************************************************\

Module: Summarizer

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SUMMARIZER_H
#define CPROVER_SUMMARIZER_H

#include <util/time_stopping.h>
#include <util/message.h>

#include <goto-programs/goto_model.h>

#include "../ssa/local_ssa.h"

class summarizert:public messaget
{
public:
  inline summarizert():
    simplify(false),
    fixed_point(false)
  {
  }
  
  bool simplify, fixed_point;

  void operator()(const goto_modelt &);
  void operator()(const goto_modelt &, const irep_idt &);

  // statistics
  absolute_timet start_time;
  time_periodt sat_time;

protected:
  void report_statistics();

  void summarize(
    const goto_modelt &,
    const goto_functionst::function_mapt::const_iterator);
};

#endif
