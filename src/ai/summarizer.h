/*******************************************************************\

Module: Summarizer

Author: Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_DELTACHECK_SUMMARIZER_H
#define CPROVER_DELTACHECK_SUMMARIZER_H

#include <util/message.h>
#include <util/options.h>
#include "ssa_inliner.h"
#include "../ssa/local_ssa.h"

#include <util/time_stopping.h>

class summarizert : public messaget
{
 public:
 summarizert(const optionst &_options, summary_storet &_summary_store) : 
    options(_options),
    summary_store(_summary_store)
  {}

  typedef summaryt::predicatet preconditiont;
  typedef irep_idt function_namet;
  typedef local_SSAt function_bodyt;
  typedef std::map<function_namet, preconditiont> preconditionst;
  typedef std::map<function_namet, function_bodyt*> functionst;
  typedef functionst::value_type functiont;

  summaryt summarize(functiont &function, const preconditiont &precondition); 
  summaryt summarize(functiont &function);

  void summarize(functionst &functions, const preconditionst &preconditions); 
  void summarize(functionst &functions); 

  void inline_summaries(const function_namet &function_name, local_SSAt::nodest &nodes, 
                        bool recursive=false);

 protected:
  const optionst &options;
  summary_storet &summary_store;
  functionst functions;
  preconditionst preconditions;

  void run();

 private:
  //typedef std::map<function_namet, bool> flag_mapt;
  //flag_mapt summary_updated;

  void compute_summary_rec(const function_namet &function_name);
};


#endif
