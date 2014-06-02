/*******************************************************************\

Module: Summarizer

Author: Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_DELTACHECK_SUMMARIZER_H
#define CPROVER_DELTACHECK_SUMMARIZER_H

#include <util/message.h>
#include "summary.h"
#include "ssa_inliner.h"
#include "../ssa/local_ssa.h"
//#include "../deltacheck/analyzer.h"

#include <util/time_stopping.h>

class summary_storet;

class summarizert : public messaget
{
 public:
 summarizert(summary_storet &_summary_store) : 
    summary_store(_summary_store), 
    inliner()
  {}

  typedef summaryt::predicatet preconditiont;
  typedef irep_idt function_namet;
  typedef local_SSAt function_bodyt;
  typedef std::map<function_namet, preconditiont> preconditionst;
  typedef std::map<function_namet, function_bodyt*> functionst;
  typedef functionst::value_type functiont;

  summaryt summarize(const functiont &function, const preconditiont &precondition); 
  summaryt summarize(const functiont &function);

  void summarize(const functionst &functions, const preconditionst &preconditions); 
  void summarize(const functionst &functions); 

  void inline_summaries(local_SSAt::nodest &nodes, bool recursive=false);

 protected:
  summary_storet &summary_store;
  ssa_inlinert inliner;
  functionst functions;
  preconditionst preconditions;

  void run();

 private:
  typedef std::map<function_namet, bool> flag_mapt;
  flag_mapt summary_updated;

  void compute_summary_rec(function_namet function_name);
};


#endif
