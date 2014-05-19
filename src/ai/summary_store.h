#ifndef CPROVER_SUMMARYSTORE_H
#define CPROVER_SUMMARYSTORE_H

#include "summarizer.h"
#include <util/std_exprt>

class summary_storet
{
 public:
  summary_storet() {}

  typedef summarizert::summaryt summaryt;
  typedef irep_idt function_namet;

  virtual void load() const {}
  virtual void save() const {}

  virtual summaryt get(function_namet function_name) const { return store[function_name]; }
  virtual bool exists(function_namet function_name) const  
    { return store.find(function_name)!=store.end(); }
  virtual void put(function_namet function_name, summaryt summary) 
    { store[function_name] = summary; }

 protected:
  std::map<function_namet, summaryt> store;

};


#endif
