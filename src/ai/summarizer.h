#ifndef CPROVER_SUMMARIZER_H
#define CPROVER_SUMMARIZER_H

#include <util/std_expr.h>

class summarizert
{
 public:
  summarizert(summary_storet &_summary_store) : summary_store(_summary_store) {}

  typedef predicatet preconditiont;
  typedef predicatet iorelationt;
  typedef std::pair<preconditiont, iorelationt> summaryt;
  typedef irep_idt function_namet;
  typedef local_SSAt function_bodyt;
  typedef std::map<function_namet, preconditiont> preconditionst;
  typedef std::map<function_namet, function_bodyt> functionst;
  typedef functionst::value_type functiont;

  summaryt summarize(functiont function, preconditiont precondition); 
  summaryt summarize(functiont function);

  void summarize(functionst functions, preconditionst preconditions); 
  void summarize(functionst functions); 

 protected:
  summary_storet &summary_store;

  void run();

  functionst functions;
  preconditionst preconditions;

 private:
  typedef std::map<function_namet, bool> flag_mapt;
  flag_mapt summary_updated;

  void compute_summary_rec(function_namet function_name);
};


#endif
